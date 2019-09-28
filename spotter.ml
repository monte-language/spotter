open CamomileLibraryDefault.Camomile;;

type monte = <
    call : string
        -> monte list
        -> (monte * monte) list
        -> monte option;
    stringOf : string;
    unwrap : monteprim option;
>
and monteprim = MNull | MBool of bool | MChar of int | MDouble of float | MInt of Z.t | MStr of string
    | MList of monte list;;

module State : sig
    type ('a, 's) t = 's -> ('a * 's)
    val run : ('a, 's) t -> 's -> ('a * 's)
    val return : 'a -> ('a, 's) t
    val map : ('a -> 'b) -> ('a, 's) t -> ('b, 's) t
    val bind : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t
    val and_then : (unit, 's) t -> ('a, 's) t -> ('a, 's) t
    val get : ('s, 's) t
    val set : 's -> (unit, 's) t
    val modify : ('s -> 's) -> (unit, 's) t
end = struct
    type ('a, 's) t = 's -> ('a * 's)
    let run ma = ma
    let return x s = (x, s)
    let map f ma s = let (x, s') = ma s in (f x, s')
    let bind ma f s = let (x, s') = ma s in f x s'
    let and_then ma mb = bind ma (fun () -> mb)
    let get s = (s, s)
    let set s _ = ((), s)
    let modify f s = ((), f s)
end;;


module type MAST = sig
    type span
    val oneToOne : (Z.t * Z.t * Z.t * Z.t) -> span
    val blob : (Z.t * Z.t * Z.t * Z.t) -> span
    type t
    type patt
    type narg
    type nparam
    type meth
    type matcher
    val nullExpr : span -> t
    val charExpr : int -> span -> t
    val doubleExpr : float -> span -> t
    val intExpr : Z.t -> span -> t
    val strExpr : string -> span -> t
    val nounExpr : string -> span -> t
    val bindingExpr : string -> span -> t
    val seqExpr : t list -> span -> t
    val callExpr : t -> string -> t list -> narg list -> span -> t
    val defExpr : patt -> t -> t -> span -> t
    val escapeExpr : patt -> t -> span -> t
    val escapeCatchExpr : patt -> t -> patt -> t -> span -> t
    val objectExpr :
        string -> patt -> t -> t list -> meth list -> matcher list ->
        span -> t
    val assignExpr : string -> t -> span -> t
    val tryExpr : t -> patt -> t -> span -> t
    val finallyExpr : t -> t -> span -> t
    val hideExpr : t -> span -> t
    val ifExpr : t -> t -> t -> span -> t
    val metaStateExpr : span -> t
    val metaContextExpr : span -> t
    val metho :
        string -> string -> patt list -> nparam list -> t -> t -> span -> meth
    val matche : patt -> t -> span -> matcher
    val namedArg : t -> t -> span -> narg
    val namedParam : t -> patt -> t -> span -> nparam
    val ignorePatt : t -> span -> patt
    val finalPatt : string -> t -> span -> patt
    val varPatt : string -> t -> span -> patt
    val listPatt : patt list -> span -> patt
    val viaPatt : t -> patt -> span -> patt
    val bindingPatt : string -> span -> patt
end;;

module Dict = Map.Make(String);;

let nullObj : monte = object
    method call verb args namedArgs = None
    method stringOf = "<null>"
    method unwrap = Some MNull
end;;

let charObj c : monte = object
    method call verb args namedArgs = match (verb, args) with
        | _ -> None
    method stringOf = Char.escaped (char_of_int c)
    method unwrap = Some (MChar c)
end;;

let doubleObj d : monte = object
    method call verb args namedArgs = match (verb, args) with
        | _ -> None
    method stringOf = string_of_float d
    method unwrap = Some (MDouble d)
end;;

let rec intObj i : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("next", []) -> Some (intObj (Z.succ i))
        | ("previous", []) -> Some (intObj (Z.pred i))
        | _ -> None
    method stringOf = Z.to_string i
    method unwrap = Some (MInt i)
end;;

let rec strObj s : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("size", []) -> Some (intObj (Z.of_int (UTF8.length s)))
        | _ -> None
    (* XXX needs quotes and escapes *)
    method stringOf = s
    method unwrap = Some (MStr s)
end;;

let rec listObj l : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("size", []) -> Some (intObj (Z.of_int (List.length l)))
        | _ -> None
    method stringOf = "[" ^ (String.concat " " (List.map (fun o -> o#stringOf) l)) ^ "]"
    method unwrap = Some (MList l)
end;;

let bindingObj slot : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("get", []) -> Some slot
        | _ -> None
    method stringOf = "<binding>"
    method unwrap = None
end;;

let finalSlotObj value : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("get", []) -> Some value
        | _ -> None
    method stringOf = "<final slot>"
    method unwrap = None
end;;

let varSlotObj value : monte = object
    val mutable cell = value
    method call verb args namedArgs = match (verb, args) with
        | ("get", []) -> Some cell
        | ("put", [v]) -> cell <- v; Some nullObj
        | _ -> None
    method stringOf = "<var slot>"
    method unwrap = None
end;;

exception Refused of (string * monte list * monte list);;

(* The main calling interface. Handles Miranda methods. Propagates exceptions
 * on failure. *)
let call_exn target verb args namedArgs : monte =
    match target#call verb args namedArgs with
        | Some rv -> rv
        | None -> match (verb, args) with
            (* Miranda behaviors. *)
            | ("_sealedDispatch", [_]) -> nullObj
            | ("_uncall", [])          -> nullObj
            | _                        -> raise (Refused (verb, args, (List.map fst namedArgs)));;
let calling verb args namedArgs target = call_exn target verb args namedArgs;;
let get = calling "get" [] [];;

let prettyPrint formatter obj = Format.pp_print_string formatter obj#stringOf;;

let input_varint ic =
    let rec go shift acc =
        let b = Z.of_int (input_byte ic) in
        let n = Z.logor acc (Z.shift_left (Z.logand b (Z.of_int 0x7f)) shift) in
        if not (Z.testbit b 7) then n else go (shift + 7) n
    in go 0 Z.zero;;

exception InvalidMAST of (string * int);;
let throw_invalid_mast ic message = raise (InvalidMAST (message, pos_in ic))

type mspan = OneToOne of (Z.t * Z.t * Z.t * Z.t)
           | Blob of (Z.t * Z.t * Z.t * Z.t)
;;
let input_span ic = match input_char ic with
    | 'S' -> OneToOne (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
    | 'B' -> Blob (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
    |  _  -> throw_invalid_mast ic "input_span"
;;
let string_of_span span =
    let sos (x1, y1, x2, y2) = String.concat ":" (List.map Z.to_string [x1; y1; x2; y2]) in
    match span with
    | OneToOne t -> "str:" ^ sos t
    | Blob     t -> "blob:" ^ sos t

exception Ejecting of (monte * monte);;
exception DoubleThrown;;
let ejectTo span : monte = object (self)
    val mutable thrown = false
    method private throw v = if thrown then raise DoubleThrown;
        thrown <- true; raise (Ejecting (v, self))
    method call verb args namedArgs = match (verb, args) with
        | ("run", [v]) -> self#throw v
        | ("run", [])  -> self#throw nullObj
        | _            -> None
    method stringOf = "<ejector at " ^ string_of_span span ^ ">"
    method unwrap = None
end;;

exception WrongType;;
let unwrapList specimen = match specimen#unwrap with
    | Some (MList l) -> l
    | _              -> raise WrongType

let const k _ = k
let rec sequence actions = match actions with
    | f :: fs -> State.bind f (fun x ->
            State.bind (sequence fs) (fun xs -> State.return (x :: xs)))
    | []      -> State.return []
let lazyState f s = f () s

exception UserException of mspan;;
module Compiler = struct
    type span = mspan
    let oneToOne t = OneToOne t
    let blob t = Blob t
    type menv = monte Dict.t
    type t = (monte, menv) State.t
    type patt = monte -> monte -> (unit, menv) State.t
    type narg = ((monte * monte), menv) State.t
    type nparam = (monte * monte) list -> (unit, menv) State.t
    type meth = (string * patt list * nparam list * t)
    type matcher = (patt * t)
    let nullExpr _ = State.return nullObj
    let charExpr c _ = State.return (charObj c)
    let doubleExpr d _ = State.return (doubleObj d)
    let intExpr i _ = State.return (intObj i)
    let strExpr s _ = State.return (strObj s)
    let nounExpr n span = State.bind State.get (fun env -> match Dict.find_opt n env with
        | Some b -> State.return (get (get b))
        | None   -> raise (UserException span))
    let bindingExpr n span = State.bind State.get (fun env -> match Dict.find_opt n env with
        | Some b -> State.return b
        | None   -> raise (UserException span))
    let seqExpr exprs _ = List.fold_left
        (fun ma expr -> State.bind ma (fun _ -> expr))
        (State.return nullObj) exprs
    let callExpr target verb args namedArgs span = State.bind target (fun t ->
        State.bind (sequence args) (fun a ->
            State.bind (sequence namedArgs) (fun na ->
                match t#call verb a na with
                    | Some o -> State.return o
                    | None   -> raise (UserException span))))
    let defExpr patt exit expr span = State.bind expr (fun e ->
        State.bind exit (fun x ->
            State.and_then (patt e x) (State.return e)))
    let escapeExpr patt body span = lazyState (fun () ->
        let ej = ejectTo span in
            State.bind (State.and_then (patt ej nullObj) State.get) (fun s ->
                try let (x, _) = body s in State.return x with
                | Ejecting (o, thrower) when thrower == ej ->
                    State.return o))
    let escapeCatchExpr patt body cpatt cbody span = lazyState (fun () ->
        let ej = ejectTo span in
            State.bind (State.and_then (patt ej nullObj) State.get) (fun s ->
                try let (x, _) = body s in State.return x with
                | Ejecting (o, thrower) when thrower == ej ->
                    State.and_then (cpatt o nullObj) cbody))
    let objectExpr doc namePatt asExpr auditors meths matchs span =
        (* XXX rebind into env *)
        State.return (object (self)
            (* XXX method dispatch, matcher dispatch *)
            method call verb args namedArgs = None
            (* XXX miranda methods *)
            (* XXX call printOn *)
            method stringOf = "<user>"
            method unwrap = None
        end)
    let assignExpr name rhs span = State.bind rhs (fun rv ->
        State.and_then (State.modify (Dict.add name rv)) (State.return rv))
    let tryExpr body patt catcher span = fun s ->
        (* XXX sealed *)
        try body s with
            | UserException _ -> State.and_then (patt nullObj nullObj) catcher s
    let finallyExpr body unwinder span = fun env ->
        try body env with
            (* XXX this would not need duplication if factored into a
             * subvariant somehow *)
            | UserException s -> unwinder env; raise (UserException s)
            | Ejecting p      -> unwinder env; raise (Ejecting p)
    let hideExpr expr _ = expr
    let ifExpr test alt cons span =
        State.bind test (fun t -> match t#unwrap with
            | Some (MBool b) -> if b then alt else cons
            | _              -> raise (UserException span))
    let metaStateExpr span = State.return (object
        method call verb args namedArgs = None
        method stringOf = "<meta.getState()>"
        method unwrap = None
    end)
    let metaContextExpr span = State.return (object
        method call verb args namedArgs = None
        method stringOf = "<meta.context()>"
        method unwrap = None
    end)
    let metho doc verb patts nparams rguard body span =
        (* XXX rguard? signature synthesis? *)
        (verb, patts, nparams, body)
    let matche patt body span = (patt, body)
    let namedArg key value span = State.bind key (fun k ->
        State.bind value (fun v -> State.return (k, v)))
    let namedParam key patt default span = fun map ->
        State.bind key (fun k ->
            (* XXX uses OCaml equality!! *)
            match List.assoc_opt k map with
                | Some value -> patt value nullObj
                | None       -> State.bind default (const (State.return ())))
    let ignorePatt guard span = fun specimen exit ->
        State.bind guard (fun g ->
            call_exn g "coerce" [specimen; exit] []; State.return ())
    let finalPatt noun guard span = fun specimen exit ->
        State.bind guard (fun g ->
            let s = call_exn g "coerce" [specimen; exit] [] in
            (* XXX guards *)
            State.modify (Dict.add noun (finalSlotObj s)))
    let varPatt noun guard span = fun specimen exit ->
        State.bind guard (fun g ->
            let s = call_exn g "coerce" [specimen; exit] [] in
            (* XXX guards *)
            State.modify (Dict.add noun (varSlotObj s)))
    let listPatt patts span = fun specimen exit ->
        let specimens = unwrapList specimen in
        List.fold_left2 (fun ma p s -> State.and_then ma (p s exit)) (State.return ()) patts specimens
    let viaPatt transformer patt span = fun specimen exit ->
        State.bind transformer (fun trans ->
            patt (call_exn trans "run" [specimen; exit] []) exit)
    let bindingPatt noun span = fun specimen exit ->
        State.modify (Dict.add noun specimen)
end;;

let input_str ic = really_input_string ic (Z.to_int (input_varint ic));;
let input_many f ic = let l = Z.to_int (input_varint ic) in List.init l (fun _ -> f ic)

(* A growing mutable list that is indexed backwards. Simulates a portion of
 * the Python list API. *)
let backlist () = object
    val mutable l = []
    val mutable len = 0
    method push x = l <- x :: l; len <- len + 1
    method get i = List.nth l (len - 1 - i)
    method tl = List.hd l
end;;

exception InvalidMagic;;
let mast_magic = "Mont\xe0MAST\x01";;
let open_in_mast path = let ic = open_in_bin path in
    (* Check the magic number. *)
    for i = 0 to String.length mast_magic - 1 do
        if input_char ic <> String.get mast_magic i then
            (close_in ic; raise InvalidMagic)
    done; ic
;;

module MASTContext (Monte : MAST) = struct
    type masthack = HExpr of Monte.t | HMeth of Monte.meth | HMatch of Monte.matcher

    let make = object (self)
        (* Compared to the classic MAST context, we store the exprs and patts
         * backwards, so that we can build them quickly. *)
        val exprs = backlist ()
        val patts = backlist ()

        method private eat_span ic = match input_char ic with
            | 'S' -> Monte.oneToOne (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
            | 'B' -> Monte.blob (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
            |  _  -> throw_invalid_mast ic "input_span"
        method private eat_expr ic = match exprs#get (Z.to_int (input_varint ic)) with
            | HExpr e -> e
            | _       -> throw_invalid_mast ic "eat_expr"
        method private eat_method ic = match exprs#get (Z.to_int (input_varint ic)) with
            | HMeth m -> m
            | _       -> throw_invalid_mast ic "eat_method"
        method private eat_matcher ic = match exprs#get (Z.to_int (input_varint ic)) with
            | HMatch m -> m
            | _        -> throw_invalid_mast ic "eat_matcher"
        method private eat_patt ic = patts#get (Z.to_int (input_varint ic))

        method private eat_tag ic = match input_char ic with
            | 'P' -> patts#push (match input_char ic with
                | 'I' -> Monte.ignorePatt (self#eat_expr ic) (self#eat_span ic)
                | 'F' -> let n = input_str ic in
                    Monte.finalPatt n (self#eat_expr ic) (self#eat_span ic)
                | 'V' -> let n = input_str ic in
                    Monte.varPatt n (self#eat_expr ic) (self#eat_span ic)
                | 'L' -> Monte.listPatt (input_many self#eat_patt ic) (self#eat_span ic)
                | 'A' -> let trans = self#eat_expr ic in
                    Monte.viaPatt trans (self#eat_patt ic) (self#eat_span ic)
                | 'B' -> Monte.bindingPatt (input_str ic) (self#eat_span ic)
                |  x  -> throw_invalid_mast ic "patt"
            )
            (* XXX code chars might not be right *)
            | 'M' -> let eat_nparam ic = Monte.namedParam (self#eat_expr ic)
                    (self#eat_patt ic) (self#eat_expr ic) (self#eat_span ic)
                in exprs#push (HMeth (Monte.metho (input_str ic) (input_str ic)
                    (input_many self#eat_patt ic) (input_many eat_nparam ic)
                    (self#eat_expr ic) (self#eat_expr ic)
                    (self#eat_span ic)))
            (* XXX this one too *)
            | 'R' -> exprs#push (HMatch
                (Monte.matche (self#eat_patt ic) (self#eat_expr ic) (self#eat_span ic)))
            | 'L' -> exprs#push (HExpr ((match input_char ic with
                | 'N' -> Monte.nullExpr
                | 'S' -> Monte.strExpr (input_str ic)
                |  x  -> throw_invalid_mast ic "literal"
            ) (self#eat_span ic)))
            |  x  -> exprs#push (HExpr ((match input_char ic with
                | 'N' -> Monte.nounExpr (input_str ic)
                | 'B' -> Monte.bindingExpr (input_str ic)
                | 'S' -> Monte.seqExpr (input_many self#eat_expr ic)
                | 'C' -> let eat_narg ic = Monte.namedArg (self#eat_expr ic)
                        (self#eat_expr ic) (self#eat_span ic) in
                    let t = self#eat_expr ic in
                    let v = input_str ic in
                    let a = input_many self#eat_expr ic in
                    let na = input_many eat_narg ic in
                    Monte.callExpr t v a na
                | 'D' -> let p = self#eat_patt ic in
                    let ex = self#eat_expr ic in
                    Monte.defExpr p ex (self#eat_expr ic)
                | 'e' -> Monte.escapeExpr (self#eat_patt ic) (self#eat_expr ic)
                | 'E' -> Monte.escapeCatchExpr (self#eat_patt ic)
                    (self#eat_expr ic) (self#eat_patt ic) (self#eat_expr ic)
                | 'A' -> let target = input_str ic in
                    Monte.assignExpr target (self#eat_expr ic)
                | 'F' -> Monte.finallyExpr (self#eat_expr ic) (self#eat_expr ic)
                | 'Y' -> Monte.tryExpr (self#eat_expr ic) (self#eat_patt ic) (self#eat_expr ic)
                | 'H' -> Monte.hideExpr (self#eat_expr ic)
                | 'I' -> let test = self#eat_expr ic in
                    let cons = self#eat_expr ic in
                    let alt = self#eat_expr ic in
                    Monte.ifExpr test cons alt
                | 'T' -> Monte.metaStateExpr
                | 'X' -> Monte.metaContextExpr
                |  x  -> throw_invalid_mast ic "eat_tag"
            ) (self#eat_span ic)))

        method eat_all_exprs ic =
            try while true do
                self#eat_tag ic
            done with | End_of_file -> ()
        method eat_last_expr ic = self#eat_all_exprs ic; match exprs#tl with
            | HExpr e -> e
            | _       -> throw_invalid_mast ic "eat_last_expr"
    end
end;;

module M = MASTContext(Compiler);;

let read_mast filename =
    let ic = open_in_mast filename in
    let context = M.make in
    let rv = context#eat_last_expr ic in
    close_in ic;
    rv;;
