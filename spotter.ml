open CamomileLibraryDefault.Camomile

let logged label ch =
  Printf.printf "%s%c..." label ch ;
  ch

type monte =
  < call: string -> monte list -> (monte * monte) list -> monte option
  ; stringOf: string
  ; unwrap: monteprim option >

and monteprim =
  | MNull
  | MBool of bool
  | MChar of int
  | MDouble of float
  | MInt of Z.t
  | MStr of string
  | MList of monte list

let to_monte
    (m :
      < call: string -> monte list -> (monte * monte) list -> monte option
      ; stringOf: string
      ; unwrap: monteprim option
      ; .. >) : monte =
  (m :> monte)

module State : sig
  type ('a, 's) t = 's -> 'a * 's

  val run : ('a, 's) t -> 's -> 'a * 's
  val return : 'a -> ('a, 's) t
  val map : ('a -> 'b) -> ('a, 's) t -> ('b, 's) t
  val bind : ('a, 's) t -> ('a -> ('b, 's) t) -> ('b, 's) t
  val and_then : (unit, 's) t -> ('a, 's) t -> ('a, 's) t
  val get : ('s, 's) t
  val set : 's -> (unit, 's) t
  val modify : ('s -> 's) -> (unit, 's) t
end = struct
  type ('a, 's) t = 's -> 'a * 's

  let run ma = ma
  let return x s = (x, s)

  let map f ma s =
    let x, s' = ma s in
    (f x, s')

  let bind ma f s =
    let x, s' = ma s in
    f x s'

  let and_then ma mb = bind ma (fun () -> mb)
  let get s = (s, s)
  let set s _ = ((), s)
  let modify f s = ((), f s)
end

module type MAST = sig
  type span

  val oneToOne : Z.t * Z.t * Z.t * Z.t -> span
  val blob : Z.t * Z.t * Z.t * Z.t -> span

  type t
  type patt
  type narg
  type nparam
  type meth
  type matcher

  val charExpr : int -> span -> t
  val doubleExpr : float -> span -> t
  val intExpr : Z.t -> span -> t
  val strExpr : string -> span -> t
  val nounExpr : string -> span -> t
  val bindingExpr : string -> span -> t
  val seqExpr : t list -> span -> t
  val callExpr : t -> string -> t list -> narg list -> span -> t
  val defExpr : patt -> t option -> t -> span -> t
  val escapeExpr : patt -> t -> span -> t
  val escapeCatchExpr : patt -> t -> patt -> t -> span -> t

  val objectExpr :
    string -> patt -> t -> t list -> meth list -> matcher list -> span -> t

  val assignExpr : string -> t -> span -> t
  val tryExpr : t -> patt -> t -> span -> t
  val finallyExpr : t -> t -> span -> t
  val hideExpr : t -> span -> t
  val ifExpr : t -> t -> t option -> span -> t
  val metaStateExpr : span -> t
  val metaContextExpr : span -> t

  val metho :
    string -> string -> patt list -> nparam list -> t -> t -> span -> meth

  val matche : patt -> t -> span -> matcher
  val namedArg : t -> t -> span -> narg
  val namedParam : t -> patt -> t option -> span -> nparam
  val ignorePatt : t option -> span -> patt
  val finalPatt : string -> t option -> span -> patt
  val varPatt : string -> t option -> span -> patt
  val listPatt : patt list -> span -> patt
  val viaPatt : t -> patt -> span -> patt
  val bindingPatt : string -> span -> patt
end

module Dict = Map.Make (String)

module AtomDict = Map.Make (struct
  type t = string * int

  let compare = compare
end)

let nullObj : monte =
  object
    method call verb args namedArgs = None

    method stringOf = "<null>"

    method unwrap = Some MNull
  end

let charObj c : monte =
  object
    method call verb args namedArgs = match (verb, args) with _ -> None

    method stringOf = Char.escaped (char_of_int c)

    method unwrap = Some (MChar c)
  end

let doubleObj d : monte =
  object
    method call verb args namedArgs = match (verb, args) with _ -> None

    method stringOf = string_of_float d

    method unwrap = Some (MDouble d)
  end

let rec intObj i : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with
      | "next", [] -> Some (intObj (Z.succ i))
      | "previous", [] -> Some (intObj (Z.pred i))
      | "add", [jj] -> (
        match jj#unwrap with
        | Some (MInt j) -> Some (intObj (Z.add i j))
        | _ -> None )
      | "multiply", [jj] -> (
        match jj#unwrap with
        | Some (MInt j) -> Some (intObj (Z.mul i j))
        | _ -> None )
      | _ -> None

    method stringOf = Z.to_string i

    method unwrap = Some (MInt i)
  end

let rec strObj s : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with
      | "size", [] -> Some (intObj (Z.of_int (UTF8.length s)))
      | _ -> None

    (* XXX needs quotes and escapes *)
    method stringOf = s

    method unwrap = Some (MStr s)
  end

let rec listObj l : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with
      | "size", [] -> Some (intObj (Z.of_int (List.length l)))
      | _ -> None

    method stringOf =
      "[" ^ String.concat " " (List.map (fun o -> o#stringOf) l) ^ "]"

    method unwrap = Some (MList l)
  end

let _makeList : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with "run", _ -> Some (listObj args) | _ -> None

    method stringOf = "_makeList"

    method unwrap = None
  end

let bindingObj slot : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with "get", [] -> Some slot | _ -> None

    method stringOf = "<binding>"

    method unwrap = None
  end

let finalSlotObj value : monte =
  object
    method call verb args namedArgs =
      match (verb, args) with "get", [] -> Some value | _ -> None

    method stringOf = "<final slot>"

    method unwrap = None
  end

let varSlotObj value : monte =
  object
    val mutable cell = value

    method call verb args namedArgs =
      match (verb, args) with
      | "get", [] -> Some cell
      | "put", [v] ->
          cell <- v ;
          Some nullObj
      | _ -> None

    method stringOf = "<var slot>"

    method unwrap = None
  end

let safeScope =
  Dict.add "null"
    (bindingObj (finalSlotObj nullObj))
    (Dict.add "_makeList" (bindingObj (finalSlotObj _makeList)) Dict.empty)

exception Refused of (string * monte list * monte list)

(* The main calling interface. Handles Miranda methods. Propagates exceptions
 * on failure. *)
let call_exn target verb args namedArgs : monte =
  match target#call verb args namedArgs with
  | Some rv -> rv
  | None -> (
    match (verb, args) with
    (* Miranda behaviors. *)
    | "_sealedDispatch", [_] -> nullObj
    | "_uncall", [] -> nullObj
    | _ -> raise (Refused (verb, args, List.map fst namedArgs)) )

let calling verb args namedArgs target = call_exn target verb args namedArgs
let get = calling "get" [] []
let prettyPrint formatter obj = Format.pp_print_string formatter obj#stringOf

let input_varint ic =
  let rec go shift acc =
    let b = Z.of_int (input_byte ic) in
    let n = Z.logor acc (Z.shift_left (Z.logand b (Z.of_int 0x7f)) shift) in
    if not (Z.testbit b 7) then n else go (shift + 7) n in
  go 0 Z.zero

exception InvalidMAST of (string * int)

let throw_invalid_mast ic message = raise (InvalidMAST (message, pos_in ic))

type mspan =
  | OneToOne of (Z.t * Z.t * Z.t * Z.t)
  | Blob of (Z.t * Z.t * Z.t * Z.t)

let input_span ic =
  match input_char ic with
  | 'S' ->
      OneToOne
        (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
  | 'B' ->
      Blob (input_varint ic, input_varint ic, input_varint ic, input_varint ic)
  | _ -> throw_invalid_mast ic "input_span"

let string_of_span span =
  let sos (x1, y1, x2, y2) =
    String.concat ":" (List.map Z.to_string [x1; y1; x2; y2]) in
  match span with OneToOne t -> "str:" ^ sos t | Blob t -> "blob:" ^ sos t

exception Ejecting of (monte * monte)
exception DoubleThrown

let ejectTo span =
  let ej =
    object (self)
      val mutable thrown = false

      method disable =
        if thrown then raise DoubleThrown ;
        thrown <- true

      method private throw v =
        self#disable ;
        raise (Ejecting (v, to_monte self))

      method call verb args namedArgs =
        match (verb, args) with
        | "run", [v] -> self#throw v
        | "run", [] -> self#throw nullObj
        | _ -> None

      method stringOf = "<ejector at " ^ string_of_span span ^ ">"

      method unwrap = None
    end in
  (to_monte ej, fun () -> ej#disable)

exception WrongType

let unwrapList specimen =
  match specimen#unwrap with Some (MList l) -> l | _ -> raise WrongType

let const k _ = k

let rec sequence actions =
  match actions with
  | f :: fs ->
      State.bind f (fun x ->
          State.bind (sequence fs) (fun xs -> State.return (x :: xs)))
  | [] -> State.return []

let lazyState f s = f () s

exception UserException of mspan

module Compiler = struct
  type span = mspan

  let oneToOne t = OneToOne t
  let blob t = Blob t

  type menv = monte Dict.t
  type t = (monte, menv) State.t
  type patt = monte -> monte -> (unit, menv) State.t
  type narg = (monte * monte, menv) State.t
  type nparam = (monte * monte) list -> (unit, menv) State.t
  type meth = string * patt list * nparam list * t
  type matcher = patt * t

  let charExpr c _ = State.return (charObj c)
  let doubleExpr d _ = State.return (doubleObj d)
  let intExpr i _ = State.return (intObj i)
  let strExpr s _ = State.return (strObj s)

  let nounExpr n span =
    State.bind State.get (fun env ->
        match Dict.find_opt n env with
        | Some b -> State.return (get (get b))
        | None -> raise (UserException span))

  let nullExpr span = nounExpr "null" span

  let bindingExpr n span =
    State.bind State.get (fun env ->
        match Dict.find_opt n env with
        | Some b -> State.return b
        | None -> raise (UserException span))

  let seqExpr exprs _ =
    List.fold_left
      (fun ma expr -> State.bind ma (fun _ -> expr))
      (State.return nullObj) exprs

  let callExpr target verb args namedArgs span =
    State.bind target (fun t ->
        State.bind (sequence args) (fun a ->
            State.bind (sequence namedArgs) (fun na ->
                match t#call verb a na with
                | Some o -> State.return o
                | None -> raise (UserException span))))

  let defExpr patt exitOpt expr span =
    State.bind expr (fun e ->
        match exitOpt with
        | Some exit ->
            State.bind exit (fun x ->
                State.and_then (patt e x) (State.return e))
        | None -> State.and_then (patt e nullObj) (State.return e))

  let escapeExpr patt body span =
    lazyState (fun () ->
        let ej, disable = ejectTo span in
        State.bind
          (State.and_then (patt ej nullObj) State.get)
          (fun s ->
            try
              let x, _ = body s in
              disable () ; State.return x
            with Ejecting (o, thrower) when thrower == ej -> State.return o))

  let escapeCatchExpr patt body cpatt cbody span =
    lazyState (fun () ->
        let ej, disable = ejectTo span in
        State.bind
          (State.and_then (patt ej nullObj) State.get)
          (fun s ->
            try
              let x, _ = body s in
              disable () ; State.return x
            with Ejecting (o, thrower) when thrower == ej ->
              State.and_then (cpatt o nullObj) cbody))

  let objectExpr doc namePatt asExpr auditors meths matchs span =
    let methdict =
      List.fold_left
        (fun d (v, ps, nps, body) ->
          AtomDict.add (v, List.length ps) (ps, nps, body) d)
        AtomDict.empty meths in
    State.bind asExpr (fun ase ->
        State.bind (sequence auditors) (fun auds (* XXX rebind into env *) s ->
            ( object (self)
                (* XXX method dispatch, matcher dispatch *)
                method call verb args namedArgs : monte option =
                  Printf.printf "call: %s/%d" verb (List.length args) ;
                  match
                    AtomDict.find_opt (verb, List.length args) methdict
                  with
                  | None ->
                      Printf.printf "no such method" ;
                      None (* refused. XXX matchers *)
                  | Some (params, nParams, body) ->
                      let exit = nullObj (* XXX *) in
                      (* XXX bind namePatt to self *)
                      (* XXX duplicate code with listPatt, refactor! *)
                      let env' =
                        List.fold_left2
                          (fun ma p s -> State.and_then ma (p s exit))
                          (State.return ()) params args in
                      Printf.printf "executing %s" verb ;
                      let o, _ = State.and_then env' body s in
                      Some o

                (* XXX miranda methods *)
                (* XXX call printOn *)
                method stringOf = "<user>"

                method unwrap = None
              end
            , s )))

  let assignExpr name rhs span =
    State.bind rhs (fun rv ->
        State.and_then (State.modify (Dict.add name rv)) (State.return rv))

  let tryExpr body patt catcher span s =
    (* XXX sealed *)
    try body s
    with UserException _ -> State.and_then (patt nullObj nullObj) catcher s

  let finallyExpr body unwinder span env =
    try body env with
    (* XXX this would not need duplication if factored into a
             * subvariant somehow *)
    | UserException s -> unwinder env ; raise (UserException s)
    | Ejecting p -> unwinder env ; raise (Ejecting p)

  let hideExpr expr _ = expr

  let ifExpr test cons alt span =
    let alt' = Option.value alt ~default:(nullExpr span) in
    State.bind test (fun t ->
        match t#unwrap with
        | Some (MBool b) -> if b then cons else alt'
        | _ -> raise (UserException span))

  let metaStateExpr span =
    State.return
      (object
         method call verb args namedArgs = None

         method stringOf = "<meta.getState()>"

         method unwrap = None
      end)

  let metaContextExpr span =
    State.return
      (object
         method call verb args namedArgs = None

         method stringOf = "<meta.context()>"

         method unwrap = None
      end)

  let metho doc verb patts nparams rguard body span =
    (* XXX rguard? signature synthesis? *)
    (verb, patts, nparams, body)

  let matche patt body span = (patt, body)

  let namedArg key value span =
    State.bind key (fun k -> State.bind value (fun v -> State.return (k, v)))

  let namedParam key patt default span map =
    State.bind key (fun k ->
        (* XXX uses OCaml equality!! *)
        match List.assoc_opt k map with
        | Some value -> patt value nullObj
        | None ->
            State.bind
              (Option.value default ~default:(nullExpr span))
              (const (State.return ())))

  let coerceOpt guardOpt specimen exit =
    match guardOpt with
    | None -> State.return specimen
    | Some guard ->
        State.bind guard (fun g ->
            let s = call_exn g "coerce" [specimen; exit] [] in
            State.return s)

  let ignorePatt guardOpt span specimen exit =
    State.bind (coerceOpt guardOpt specimen exit) (fun _prize ->
        State.return ())

  let finalPatt noun guard span specimen exit =
    State.bind (coerceOpt guard specimen exit) (fun s ->
        (* XXX guards *)
        State.modify (Dict.add noun (bindingObj (finalSlotObj s))))

  let varPatt noun guard span specimen exit =
    State.bind (coerceOpt guard specimen exit) (fun s ->
        (* XXX guards *)
        State.modify (Dict.add noun (bindingObj (varSlotObj s))))

  let listPatt patts span specimen exit =
    let specimens = unwrapList specimen in
    List.fold_left2
      (fun ma p s -> State.and_then ma (p s exit))
      (State.return ()) patts specimens

  let viaPatt transformer patt span specimen exit =
    State.bind transformer (fun trans ->
        patt (call_exn trans "run" [specimen; exit] []) exit)

  let bindingPatt noun span specimen exit =
    State.modify (Dict.add noun specimen)
end

let input_str ic = really_input_string ic (Z.to_int (input_varint ic))

let input_many f ic =
  let l = Z.to_int (input_varint ic) in
  List.init l (fun _ -> f ic)

(* A growing mutable list that is indexed backwards. Simulates a portion of
 * the Python list API. *)
let backlist () =
  object
    val mutable l = []

    val mutable len = 0

    method push x =
      l <- x :: l ;
      len <- len + 1

    method get i = List.nth l (len - 1 - i)

    method tl = List.hd l
  end

exception InvalidMagic

let mast_magic = "Mont\xe0MAST\x01"

let open_in_mast path =
  let ic = open_in_bin path in
  (* Check the magic number. *)
  for i = 0 to String.length mast_magic - 1 do
    if input_char ic <> mast_magic.[i] then (close_in ic ; raise InvalidMagic)
  done ;
  ic

module MASTContext (Monte : MAST) = struct
  type masthack =
    | HNone
    | HExpr of Monte.t
    | HMeth of Monte.meth
    | HMatch of Monte.matcher

  let v4 ic =
    let i1 = input_varint ic in
    let i2 = input_varint ic in
    let i3 = input_varint ic in
    let i4 = input_varint ic in
    Printf.printf "i4:%s,%s,%s,%s\n" (Z.to_string i1) (Z.to_string i2)
      (Z.to_string i3) (Z.to_string i4) ;
    (i1, i2, i3, i4)

  let make =
    object (self)
      (* Compared to the classic MAST context, we store the exprs and patts
         * backwards, so that we can build them quickly. *)
      val exprs = backlist ()

      val patts = backlist ()

      method private eat_span ic =
        match input_char ic with
        | 'S' -> Monte.oneToOne (v4 ic)
        | 'B' -> Monte.blob (v4 ic)
        | _ -> throw_invalid_mast ic "input_span"

      method private eat_expr ic =
        match exprs#get (Z.to_int (input_varint ic)) with
        | HExpr e -> e
        | _ -> throw_invalid_mast ic "eat_expr"

      method eat_expr_opt ic =
        match exprs#get (Z.to_int (input_varint ic)) with
        | HExpr e -> Some e
        | HNone -> None
        | _ -> throw_invalid_mast ic "eat_expr_opt"

      method private eat_method ic =
        match exprs#get (Z.to_int (input_varint ic)) with
        | HMeth m -> m
        | _ -> throw_invalid_mast ic "eat_method"

      method private eat_matcher ic =
        match exprs#get (Z.to_int (input_varint ic)) with
        | HMatch m -> m
        | _ -> throw_invalid_mast ic "eat_matcher"

      method private eat_patt ic = patts#get (Z.to_int (input_varint ic))

      method private eat_tag ic =
        match logged "eat_tag" (input_char ic) with
        | 'P' ->
            patts#push
              ( match logged "Pattern tag" (input_char ic) with
              | 'I' ->
                  let g = self#eat_expr_opt ic in
                  Monte.ignorePatt g (self#eat_span ic)
              | 'F' ->
                  let n = input_str ic in
                  let g = self#eat_expr_opt ic in
                  Monte.finalPatt n g (self#eat_span ic)
              | 'V' ->
                  let n = input_str ic in
                  let g = self#eat_expr_opt ic in
                  Monte.varPatt n g (self#eat_span ic)
              | 'L' ->
                  let ps = input_many self#eat_patt ic in
                  Monte.listPatt ps (self#eat_span ic)
              | 'A' ->
                  let trans = self#eat_expr ic in
                  let p = self#eat_patt ic in
                  Monte.viaPatt trans p (self#eat_span ic)
              | 'B' ->
                  let s = input_str ic in
                  Monte.bindingPatt s (self#eat_span ic)
              | x -> throw_invalid_mast ic "patt" )
        (* XXX code chars might not be right *)
        | 'M' ->
            let eat_nparam ic =
              let ek = self#eat_expr ic
              and pv = self#eat_patt ic
              and ed = self#eat_expr_opt ic in
              Monte.namedParam ek pv ed (self#eat_span ic) in
            let doc = input_str ic
            and verb = input_str ic
            and ps = input_many self#eat_patt ic
            and nps = input_many eat_nparam ic
            and g = self#eat_expr ic
            and b = self#eat_expr ic in
            exprs#push
              (HMeth (Monte.metho doc verb ps nps g b (self#eat_span ic)))
        (* XXX this one too *)
        | 'R' ->
            let p = self#eat_patt ic and e = self#eat_expr ic in
            exprs#push (HMatch (Monte.matche p e (self#eat_span ic)))
        | 'L' ->
            exprs#push
              ( match logged "literal tag" (input_char ic) with
              | 'N' ->
                  ignore (self#eat_span ic) ;
                  HNone
              | tag ->
                  let e =
                    match tag with
                    | 'I' ->
                        let i = input_varint ic in
                        let shifted = Z.shift_right i 1 in
                        Monte.intExpr
                          ( if Z.testbit i 0 then
                            Z.logxor (Z.of_int (-1)) shifted
                          else shifted )
                    | 'S' -> Monte.strExpr (input_str ic)
                    | x -> throw_invalid_mast ic ("literal:" ^ Char.escaped x)
                  in
                  HExpr (e (self#eat_span ic)) )
        | tag ->
            let expr =
              match logged "expr tag" tag with
              | 'N' -> Monte.nounExpr (input_str ic)
              | 'B' -> Monte.bindingExpr (input_str ic)
              | 'S' -> Monte.seqExpr (input_many self#eat_expr ic)
              | 'C' ->
                  let eat_narg ic =
                    let n = self#eat_expr ic in
                    let v = self#eat_expr ic in
                    Monte.namedArg n v (self#eat_span ic) in
                  let t = self#eat_expr ic in
                  let v = input_str ic in
                  let a = input_many self#eat_expr ic in
                  let na = input_many eat_narg ic in
                  Monte.callExpr t v a na
              | 'D' ->
                  let p = self#eat_patt ic in
                  let ex = self#eat_expr_opt ic in
                  Monte.defExpr p ex (self#eat_expr ic)
              | 'e' ->
                  let p = self#eat_patt ic in
                  Monte.escapeExpr p (self#eat_expr ic)
              | 'E' ->
                  let p = self#eat_patt ic in
                  let e = self#eat_expr ic in
                  let pc = self#eat_patt ic in
                  let ec = self#eat_expr ic in
                  Monte.escapeCatchExpr p e pc ec
              | 'O' ->
                  (* Object with no script, just direct methods and matchers. *)
                  let doc = input_str ic
                  and patt = self#eat_patt ic
                  and asExpr = self#eat_expr ic
                  and implements = input_many self#eat_expr ic
                  and methods = input_many self#eat_method ic
                  and matchers = input_many self#eat_matcher ic in
                  Monte.objectExpr doc patt asExpr implements methods matchers
              | 'A' ->
                  let target = input_str ic in
                  Monte.assignExpr target (self#eat_expr ic)
              | 'F' ->
                  let eb = self#eat_expr ic in
                  let ec = self#eat_expr ic in
                  Monte.finallyExpr eb ec
              | 'Y' ->
                  let eb = self#eat_expr ic in
                  let p = self#eat_patt ic in
                  let ec = self#eat_expr ic in
                  Monte.tryExpr eb p ec
              | 'H' -> Monte.hideExpr (self#eat_expr ic)
              | 'I' ->
                  let test = self#eat_expr ic in
                  let cons = self#eat_expr ic in
                  let alt = self#eat_expr_opt ic in
                  Monte.ifExpr test cons alt
              | 'T' -> Monte.metaStateExpr
              | 'X' -> Monte.metaContextExpr
              | x -> throw_invalid_mast ic ("eat_tag:" ^ Char.escaped x) in
            exprs#push (HExpr (expr (self#eat_span ic)))

      method eat_all_exprs ic =
        try
          while true do
            self#eat_tag ic
          done
        with End_of_file -> ()

      method eat_last_expr ic =
        self#eat_all_exprs ic ;
        match exprs#tl with
        | HExpr e -> e
        | _ -> throw_invalid_mast ic "eat_last_expr"
    end
end

module M = MASTContext (Compiler)

let read_mast filename =
  let ic = open_in_mast filename in
  let context = M.make in
  let rv = context#eat_last_expr ic in
  close_in ic ; rv

let safeScope = Dict.add "null" (bindingObj (finalSlotObj nullObj)) Dict.empty

let () =
  for i = 1 to Array.length Sys.argv - 1 do
    Printf.printf "[%i] %s\n" i Sys.argv.(i) ;
    let filename = Sys.argv.(i) in
    let expr = read_mast filename in
    try
      let result, _ = expr safeScope in
      Printf.printf "==> %s\n" result#stringOf
    with
    | Refused (verb, args, namedArgs) ->
        Printf.printf "Refused: XXX.%s(...)\n" verb
    | UserException span ->
        Printf.printf "UserException at %s\n" (string_of_span span)
  done
