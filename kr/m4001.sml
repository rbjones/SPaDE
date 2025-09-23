(* SML translation of kr/h4001.md HOL datatypes *)

(* Names *)
datatype sname =  Sn of string
datatype rname = Rn of int * (sname * int) list;

(* HName Trees *)
datatype 'a hntree =
    Hnt of sname * (('a hntree list) list)
  | Hleaf of 'a;

(* Types *)
datatype htype =
    Tyv of sname
  | Tyc of rname * htype list;

(* Terms *)
datatype hterm =
    Tmv of rname * htype
  | Tmc of rname * htype
  | Tapp of hterm * hterm
  | Tabs of sname * htype * hterm
  | Trel of rname * hterm
  | Tloc of rname * hterm;

(* Sequents *)
datatype hsequent = Sg of hterm list * hterm;
