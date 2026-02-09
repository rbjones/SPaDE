app load ["bossLib", "stringTheory"];
open bossLib Theory Parse;
local open stringTheory pred_setTheory in end;
val _ = new_theory "SPaDE_KR_Spec";

Datatype: sexp =
      Atom string
    | Nil
    | Cons sexp sexp
End

val _ = Datatype `sname = Sn string`;
val _ = Datatype `rname = Rn num (sname list)`;

val _ = Datatype `shash = Sh string`;

val _ = Datatype
        `htype = Tyv sname
               | Tyc rname (htype list)`;

val _ = Datatype
      `hterm = Tmv sname
             | Tmc rname htype
             | Tapp hterm hterm
             | Tabs sname htype hterm`;             

val _ = Datatype
      `hsequent = Sg (hterm list) hterm`;

Datatype: hsig =
      <| types: (rname # num)list;
         constants: (rname # htype)list
      |>
End

Datatype: hext =
      <| signature: hsig;
         constraint: hterm
      |>
End

Datatype: htheory =
      <| Thname: sname;
         Parents: rname list # shash;
         Extensions: hext list;
         Shash: shash
      |>
End

val _ = Datatype ('a)`folder = Sdict (sname # 'a) list`;

val _ = Datatype
 `('a)rtree =
   Sfolder ('a rtree) folder   |
   Rleaf 'a`;

val _ = Datatype `hrepo = Hrepo ((htheory folder) rtree)`;

