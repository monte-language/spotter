open CamomileLibraryDefault.Camomile;;

type monte = <
    call : string
        -> monte list
        -> (monte * monte) list
        -> monte option;
    stringOf : string;
>;;

let nullObj : monte = object
    method call verb args namedArgs = None
    method stringOf = "<null>"
end;;

let rec intObj i : monte = object
    method call verb args namedArgs = match (verb, args) with
        | ("next", []) -> Some (intObj (i + 1))
        | ("previous", []) -> Some (intObj (i - 1))
        | _ -> None
    method stringOf = string_of_int i
end;;

exception Refused of (string * monte list * monte list);;

let call_exn target verb args namedArgs : monte =
    match target#call verb args namedArgs with
        | Some rv -> rv
        | None -> raise (Refused (verb, args, (List.map fst namedArgs)));;

let prettyPrint formatter obj = Format.pp_print_string formatter obj#stringOf;;

type
mastexpr = NullExpr
         | LiteralExpr of monte
         | CharExpr of string
         | DoubleExpr of float
         | IntExpr of Z.t
         | StringExpr of string
         | NounExpr of string
         | BindingExpr of string
         | SeqExpr of mastexpr list
         | CallExpr of (mastexpr * string * mastexpr list * mastnarg list)
         | DefExpr of (mastpatt * mastexpr * mastexpr)
         | EscapeExpr of (mastpatt * mastexpr)
         | EscapeCatchExpr of (mastpatt * mastexpr * mastpatt * mastexpr)
         | ObjectExpr of (string * mastpatt * mastexpr * mastexpr list * mastmethod list * mastmatcher list)
         | AssignExpr of (string * mastexpr)
         | FinallyExpr of (mastexpr * mastexpr)
         | TryExpr of (mastexpr * mastpatt * mastexpr)
         | HideExpr of mastexpr
         | IfExpr of (mastexpr * mastexpr * mastexpr)
         | MetaStateExpr
         | MetaContextExpr
and
mastmethod = (string * string * mastpatt list * mastnpatt list * mastpatt * mastpatt)
and
mastmatcher = (mastpatt * mastexpr)
and
mastnarg = (mastexpr * mastexpr)
and
mastnpatt = (mastexpr * mastpatt * mastexpr)
and
mastpatt = IgnorePattern of mastexpr
         | FinalPattern of (string * mastexpr)
         | VarPattern of (string * mastexpr)
         | ListPattern of mastpatt list
         | ViaPattern of (mastexpr * mastpatt)
         | BindingPatt of string
;;

exception InvalidMAST of string;;

let scan_varint ib =
    let rec go shift acc = Scanf.bscanf ib "%c" (fun c ->
        let b = Z.of_int (int_of_char c) in
        let n = Z.logor acc (Z.shift_left (Z.logand b (Z.of_int 0x7f)) shift) in
        if not (Z.testbit b 7) then n else go (shift + 7) n
    ) in go 0 Z.zero;;

type span = OneToOne of (Z.t * Z.t * Z.t * Z.t)
          | Blob of (Z.t * Z.t * Z.t * Z.t)
;;
let scan_span ib = Scanf.bscanf ib "%1[SB]%r%r%r%r" scan_varint scan_varint
    scan_varint scan_varint (fun c i1 i2 i3 i4 -> match c with
        | "S" -> OneToOne (i1, i2, i3, i4)
        | "B" -> Blob (i1, i2, i3, i4)
        (* This match is impossible because of the earlier range restriction. *)
        |  x -> raise (InvalidMAST x)
);;

let scan_expr ib = Scanf.bscanf ib "%c" (fun c -> match c with
    | 'L' -> Scanf.bscanf ib "%c" (fun c -> match c with
        | 'N' -> NullExpr
        |  x  -> raise (InvalidMAST (String.make 1 x)))
    |  x  -> raise (InvalidMAST (String.make 1 x)))
;;

let monte_of_mast ib = Scanf.bscanf ib "%r%r" scan_expr scan_span
    (fun expr sp -> (expr, sp));;

let read_mast filename =
    let ic = open_in_bin filename in
    let ib = Scanf.Scanning.from_channel ic in
    (* Check the magic number. *)
    Scanf.bscanf ib "Mont\xe0MAST\x01" ();
    let rv = monte_of_mast ib in
    close_in ic;
    rv;;
