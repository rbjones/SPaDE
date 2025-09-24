(* ========================================================================= *)
(* SML Signatures for ProofPower HOL to SPaDE Repository Export             *)
(* ========================================================================= *)
(* This file contains the complete signature specifications for all          *)
(* functions required to export ProofPower theories to SPaDE repositories   *)
(* as specified in SPaDEppScrape.md and ppholinterface.md                   *)
(* ========================================================================= *)

(* Required datatypes from SPaDE HOL abstract syntax (from m4001.sml) *)
(* These should be available via: use "m4001.sml"; *)

(* Additional datatypes for ProofPower interface *)
datatype DEST_SIMPLE_TYPE =
    Vartype of string
  | Ctype of (string * TYPE list)

datatype DEST_SIMPLE_TERM =
    Var of string * TYPE
  | Const of string * TYPE  
  | App of TERM * TERM
  | SimpleAbs of TERM * TERM

type SEQ = (TERM list) * TERM

(* Repository state management types *)
type repo_position = int
type theory_map = (string * repo_position) list
type repo_state = {
    output_stream : BinIO.outstream,
    current_pos : repo_position,
    theory_positions : theory_map
}

(* Exception types for error handling *)
exception ExportError of string
exception TheoryNotFound of string
exception InvalidTheoryOrder of string list

(* ========================================================================= *)
(* PROOFPOWER INTERFACE SIGNATURES                                          *)
(* ========================================================================= *)

(* Theory discovery and hierarchy functions *)
val get_theory_names : unit -> string list
val get_ancestors : string -> string list  
val get_parents : string -> string list
val get_children : string -> string list

(* Theory component extraction functions *)
val get_types : string -> TYPE list
val get_type_arity : string -> int option
val get_consts : string -> TERM list
val get_defns : string -> (string list * THM) list
val get_defn : string -> string -> THM
val get_axioms : string -> (string list * THM) list
val get_thms : string -> (string list * THM) list

(* Object decomposition functions *)
val dest_thm : THM -> SEQ
val asms : THM -> TERM list
val concl : THM -> TERM
val dest_simple_type : TYPE -> DEST_SIMPLE_TYPE
val dest_simple_term : TERM -> DEST_SIMPLE_TERM

(* Type and term classification functions *)
val is_vartype : TYPE -> bool
val is_ctype : TYPE -> bool
val is_var : TERM -> bool
val is_const : TERM -> bool
val is_app : TERM -> bool
val is_abs : TERM -> bool

(* Detailed decomposition functions *)
val dest_vartype : TYPE -> string
val dest_ctype : TYPE -> string * TYPE list
val dest_var : TERM -> string * TYPE
val dest_const : TERM -> string * TYPE
val dest_app : TERM -> TERM * TERM
val dest_abs : TERM -> TERM * TERM

(* ========================================================================= *)
(* SPADE REPOSITORY WRITING SIGNATURES                                      *)
(* ========================================================================= *)

(* Repository initialization and finalization *)
val init_repository : string -> repo_state
val finalize_repository : repo_state -> unit

(* Basic repository writing primitives *)
val write_nil : repo_state -> repo_state
val write_atom : repo_state -> string -> repo_state
val write_cons : repo_state -> repo_state

(* SPaDE data structure writing *)
val write_htype : repo_state -> htype -> repo_state
val write_hterm : repo_state -> hterm -> repo_state
val write_hsequent : repo_state -> hsequent -> repo_state
val write_signature : repo_state -> (string * htype) list -> repo_state
val write_constraint : repo_state -> hterm -> repo_state

(* Theory component writing *)
val write_theory_parents : repo_state -> (string * repo_position) list -> repo_state
val write_extension : repo_state -> (string * htype) list -> hterm -> repo_state
val write_theory : repo_state -> string -> (string list * THM) list -> 
                  (string list * THM) list -> repo_state

(* Repository folder management *)
val write_folder_header : repo_state -> repo_state
val write_folder_entry : repo_state -> string -> repo_position -> repo_state
val finalize_folder : repo_state -> repo_state

(* ========================================================================= *)
(* CONVERSION FUNCTION SIGNATURES                                           *)
(* ========================================================================= *)

(* ProofPower to SPaDE object conversion *)
val pp_type_to_htype : TYPE -> htype
val pp_term_to_hterm : TERM -> hterm
val pp_thm_to_hsequent : THM -> hsequent

(* Definition analysis and extraction *)
val extract_signature : (string list * THM) -> (string * htype) list
val extract_constraint : (string list * THM) -> hterm
val classify_tag : string -> [`TYPE of int | `CONST of htype]

(* Theory processing utilities *)
val topological_sort : string list -> string list
val gather_theory_extensions : string -> ((string * htype) list * hterm) list
val gather_theory_axioms : string -> hterm list

(* ========================================================================= *)
(* MAIN EXPORT ORCHESTRATION SIGNATURES                                     *)
(* ========================================================================= *)

(* Top-level export functions *)
val scrape_pp_theories : string -> string list -> unit
val scrape_pp_db : string -> unit

(* Theory processing functions *)
val process_theory : repo_state -> string -> repo_state
val process_theory_list : repo_state -> string list -> repo_state

(* Utility and validation functions *)
val validate_theory_order : string list -> bool
val compute_theory_dependencies : string list -> string list
val estimate_repository_size : string list -> int

(* ========================================================================= *)
(* DOCUMENTATION AND USAGE NOTES                                            *)
(* ========================================================================= *)

(*
USAGE OVERVIEW:

1. Top-level export functions:
   - scrape_pp_db: Export entire ProofPower database
   - scrape_pp_theories: Export specific list of theories

2. Core workflow:
   a) Initialize repository with init_repository
   b) Get and sort theory names with topological_sort
   c) Process each theory with process_theory
   d) Finalize repository with finalize_repository

3. Theory processing per theory:
   a) Extract theory components with get_defns, get_axioms
   b) Convert to SPaDE format with pp_*_to_h* functions
   c) Write to repository with write_theory

4. Error handling:
   - ExportError: General export failures
   - TheoryNotFound: Missing theories
   - InvalidTheoryOrder: Dependency order violations

IMPLEMENTATION REQUIREMENTS:

- All ProofPower interface functions must call appropriate ProofPower API
- Repository writing must use postfix format matching m4002.sml structure  
- Conversion functions must map ProofPower concrete syntax to SPaDE abstract syntax
- Theory ordering must respect dependency relationships
- Repository state must track positions for cross-references

See ppholinterface.md and SPaDEppScrape.md for detailed specifications.
*)