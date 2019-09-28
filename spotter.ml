open CamomileLibraryDefault.Camomile;;

let logged label ch = Printf.printf "%s%c..." label ch; ch;;

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
    method call verb args namedArgs = match (verb, args) with
      | ("coerce", [specimen; _ej]) -> Some specimen
      | _ -> None
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
let input_span ic = match (logged "Span tag" (input_char ic)) with
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

exception UserException of mspan;;
module Compiler = struct
    type span = mspan
    let oneToOne t = OneToOne t
    let blob t = Blob t
    type t = monte Dict.t -> monte
    type patt = monte Dict.t -> monte -> monte -> monte Dict.t
    type narg = monte Dict.t -> (monte * monte)
    type nparam = monte Dict.t -> (monte * monte) list -> monte Dict.t
    type meth = (string * patt list * nparam list * t)
    type matcher = (patt * t)
    let nullExpr _ = fun _ -> nullObj
    let charExpr c _ = fun _ -> charObj c
    let doubleExpr d _ = fun _ -> doubleObj d
    let intExpr i _ = fun _ -> intObj i
    let strExpr s _ = fun _ -> strObj s
    let nounExpr n span = fun env -> match Dict.find_opt n env with
        | Some b -> get (get b)
        | None   -> raise (UserException span)
    let bindingExpr n span = fun env -> match Dict.find_opt n env with
        | Some b -> b
        | None   -> raise (UserException span)
    let seqExpr exprs _ =
        fun env -> List.fold_left (fun _ s -> s env) nullObj exprs
    let callExpr target verb args namedArgs span = fun env ->
        let t = target env in
        let a = List.map (fun f -> f env) args in
        let na = List.map (fun d -> d env) namedArgs in
        match t#call verb a na with
            | Some o -> o
            | None   -> raise (UserException span)
    let defExpr patt exit expr span = fun env ->
        (* XXX clearly we don't thread state correctly! *)
        let rv = expr env in patt env (expr env) (exit env); rv
    let escapeExpr patt body span = fun env -> let ej = ejectTo span in
        try body (patt env ej nullObj) with
        | Ejecting (o, thrower) when thrower == ej -> o
    let escapeCatchExpr patt body cpatt cbody span = fun env -> let ej = ejectTo span in
        try body (patt env ej nullObj) with
        | Ejecting (o, thrower) when thrower == ej ->
                cbody (cpatt env o nullObj)
    let objectExpr doc namePatt asExpr auditors meths matchs span =
        fun env -> object (self)
            (* XXX method dispatch, matcher dispatch *)
            method call verb args namedArgs = None
            (* XXX miranda methods *)
            (* XXX call printOn *)
            method stringOf = "<user>"
            method unwrap = None
        end
    let assignExpr name rhs span = fun env ->
        let rv = rhs env in Dict.add name rv env; rv
    let tryExpr body patt catcher span = fun env ->
        (* XXX sealed *)
        try body env with
            | UserException _ -> catcher (patt env nullObj nullObj)
    let finallyExpr body unwinder span = fun env ->
        try body env with
            (* XXX this would not need duplication if factored into a
             * subvariant somehow *)
            | UserException s -> unwinder env; raise (UserException s)
            | Ejecting p      -> unwinder env; raise (Ejecting p)
    let hideExpr expr _ = expr
    let ifExpr test alt cons span = fun env -> match (test env)#unwrap with
        | Some (MBool b) -> if b then alt env else cons env
        | _              -> raise (UserException span)
    let metaStateExpr span = fun env -> object
        method call verb args namedArgs = None
        method stringOf = "<meta.getState()>"
        method unwrap = None
    end
    let metaContextExpr span = fun env -> object
        method call verb args namedArgs = None
        method stringOf = "<meta.context()>"
        method unwrap = None
    end
    let metho doc verb patts nparams rguard body span =
        (* XXX rguard? signature synthesis? *)
        (verb, patts, nparams, body)
    let matche patt body span = (patt, body)
    let namedArg key value span = fun env -> (key env, value env)
    let namedParam key patt default span = fun env map ->
        (* XXX uses OCaml equality!! *)
        match List.assoc_opt (key env) map with
            | Some value -> patt env value nullObj
            | None       -> default env; env
    let ignorePatt guard span = fun env specimen exit ->
        call_exn (guard env) "coerce" [specimen; exit] []; env
    let finalPatt noun guard span = fun env specimen exit ->
        let s = call_exn (guard env) "coerce" [specimen; exit] [] in
        (* XXX guards *)
        Dict.add noun (finalSlotObj s) env
    let varPatt noun guard span = fun env specimen exit ->
        let s = call_exn (guard env) "coerce" [specimen; exit] [] in
        (* XXX guards *)
        Dict.add noun (varSlotObj s) env
    let listPatt patts span = fun env specimen exit ->
        let specimens = unwrapList specimen in
        List.fold_left2 (fun e p s -> p e s exit) env patts specimens
    let viaPatt trans patt span = fun env specimen exit ->
        patt env (call_exn (trans env) "run" [specimen; exit] []) exit
    let bindingPatt noun span = fun env specimen exit ->
        Dict.add noun specimen env
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

    let v4 ic =
      let i1 = input_varint ic in
      let i2 = input_varint ic in
      let i3 = input_varint ic in
      let i4 = input_varint ic in
      Printf.printf "i4:%s,%s,%s,%s\n" (Z.to_string i1) (Z.to_string i2) (Z.to_string i3) (Z.to_string i4);
      (i1, i2, i3, i4)

    let make = object (self)
        (* Compared to the classic MAST context, we store the exprs and patts
         * backwards, so that we can build them quickly. *)
        val exprs = backlist ()
        val patts = backlist ()

        method private eat_span ic = match (logged "eat_span" (input_char ic)) with
            | 'S' -> Monte.oneToOne (v4 ic)
            | 'B' -> Monte.blob (v4 ic)
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
            | 'P' -> patts#push (match (logged "Pattern tag" (input_char ic)) with
                | 'I' -> let g = self#eat_expr ic in Monte.ignorePatt g (self#eat_span ic)
                | 'F' -> let n = input_str ic in
                         let e = self#eat_expr ic in
                    Monte.finalPatt n e (self#eat_span ic)
                | 'V' -> let n = input_str ic in
                         let e = self#eat_expr ic in
                    Monte.varPatt n e (self#eat_span ic)
                | 'L' -> let ps = input_many self#eat_patt ic in Monte.listPatt ps (self#eat_span ic)
                | 'A' -> let trans = self#eat_expr ic in
                         let p = self#eat_patt ic in
                    Monte.viaPatt trans p (self#eat_span ic)
                | 'B' -> let s = (input_str ic) in Monte.bindingPatt s (self#eat_span ic)
                |  x  -> throw_invalid_mast ic "patt"
            )
            (* XXX code chars might not be right *)
            | 'M' -> let eat_nparam ic =
                       let ek = self#eat_expr ic
                       and pv = self#eat_patt ic
                       and ed = self#eat_expr ic in
                       Monte.namedParam ek pv ed (self#eat_span ic)
                     in
                     let doc = (input_str ic)
                     and verb =  (input_str ic)
                     and ps = input_many self#eat_patt ic
                     and nps = input_many eat_nparam ic
                     and g = self#eat_expr ic
                     and b = self#eat_expr ic
                     in exprs#push (HMeth (Monte.metho doc verb ps nps g b (self#eat_span ic)))
            (* XXX this one too *)
            | 'R' ->
               let p = self#eat_patt ic
               and e = self#eat_expr ic
               in exprs#push (HMatch (Monte.matche p e (self#eat_span ic)))
            | 'L' -> Printf.printf "Literal..."; exprs#push (let e = match input_char ic with
                | 'N' -> Monte.nullExpr
                | 'S' -> Monte.strExpr (input_str ic)
                |  x  -> throw_invalid_mast ic ("literal:" ^ Char.escaped x)
                       in (HExpr (e (self#eat_span ic))))
            |  tag  -> let expr = match tag with
                | 'N' -> Monte.nounExpr (input_str ic)
                | 'B' -> Monte.bindingExpr (input_str ic)
                | 'S' -> Monte.seqExpr (input_many self#eat_expr ic)
                | 'C' -> let eat_narg ic =
                           let n = (self#eat_expr ic) in
                           let v = (self#eat_expr ic) in
                           Monte.namedArg n v (self#eat_span ic) in
                    let t = self#eat_expr ic in
                    let v = input_str ic in
                    let a = input_many self#eat_expr ic in
                    let na = input_many eat_narg ic in
                    Monte.callExpr t v a na
                | 'D' -> let p = self#eat_patt ic in
                    let ex = self#eat_expr ic in
                    Monte.defExpr p ex (self#eat_expr ic)
                | 'e' -> let p = self#eat_patt ic in Monte.escapeExpr p (self#eat_expr ic)
                | 'E' -> let p = self#eat_patt ic in
                         let e = self#eat_expr ic in
                         let pc = self#eat_patt ic in
                         let ec = self#eat_expr ic in
                         Monte.escapeCatchExpr p e pc ec
                | 'O' -> (* Object with no script, just direct methods and matchers. *)
                   let doc = input_str ic
                   and patt = self#eat_patt ic
                   and asExpr = self#eat_expr ic
                   and implements = input_many self#eat_expr ic
                   and methods = input_many self#eat_method ic
                   and matchers = input_many self#eat_matcher ic
                   in Monte.objectExpr doc patt asExpr implements methods matchers
                | 'A' -> let target = input_str ic in
                    Monte.assignExpr target (self#eat_expr ic)
                | 'F' -> let eb = (self#eat_expr ic) in
                         let ec = (self#eat_expr ic) in
                         Monte.finallyExpr eb ec
                | 'Y' -> let eb = self#eat_expr ic in
                         let p = self#eat_patt ic in
                         let ec = self#eat_expr ic in
                         Monte.tryExpr eb p ec
                | 'H' -> Monte.hideExpr (self#eat_expr ic)
                | 'I' -> let test = self#eat_expr ic in
                    let cons = self#eat_expr ic in
                    let alt = self#eat_expr ic in
                    Monte.ifExpr test cons alt
                | 'T' -> Monte.metaStateExpr
                | 'X' -> Monte.metaContextExpr
                |  x  -> throw_invalid_mast ic ("eat_tag:" ^ (Char.escaped x))
                     in exprs#push (HExpr (expr (self#eat_span ic)))

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
