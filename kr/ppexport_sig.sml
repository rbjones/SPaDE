(* SML Signatures for ProofPower HOL to SPaDE Repository Export *)
(* This file contains the complete signature specifications for all functions *)
(* required to export ProofPower theories to SPaDE native repositories *)

(* ===================================================================== *)
(* DATATYPES FOR PROOFPOWER INTERFACE *)
(* ===================================================================== *)

(* Datatypes for deconstructed ProofPower objects *)
datatype DEST_SIMPLE_TYPE =
    Vartype of string
  | Ctype of (string * TYPE list);

datatype DEST_SIMPLE_TERM =
    Var of string * TYPE
  | Const of string * TYPE
  | App of TERM * TERM
  | SimpleAbs of TERM * TERM;

(* Sequent type for theorem decomposition *)
type SEQ = (TERM list) * TERM;

(* ===================================================================== *)
(* PROOFPOWER INTERFACE SIGNATURES *)
(* ===================================================================== *)

signature PROOFPOWER_INTERFACE = sig
    
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
end;

(* ===================================================================== *)
(* SPADE REPOSITORY WRITING SIGNATURES *)
(* ===================================================================== *)

signature SPADE_REPO_WRITER = sig
    
    (* Repository position tracking *)
    type repo_position = int
    type theory_map = (string * repo_position) list
    
    (* Repository writing state *)
    type repo_state = {
        output_stream : BinIO.outstream,
        current_pos : repo_position,
        theory_positions : theory_map
    }
    
    (* Initialize and finalize repository *)
    val init_repository : string -> repo_state
    val finalize_repository : repo_state -> unit
    
    (* Write basic repository structures *)
    val write_nil : repo_state -> repo_state
    val write_atom : repo_state -> string -> repo_state
    val write_cons : repo_state -> repo_state
    
    (* Write SPaDE data structures *)
    val write_htype : repo_state -> htype -> repo_state
    val write_hterm : repo_state -> hterm -> repo_state
    val write_hsequent : repo_state -> hsequent -> repo_state
    val write_signature : repo_state -> (string * htype) list -> repo_state
    val write_constraint : repo_state -> hterm -> repo_state
    
    (* Write theory components *)
    val write_theory_parents : repo_state -> (string * repo_position) list -> repo_state
    val write_extension : repo_state -> (string * htype) list -> hterm -> repo_state
    val write_theory : repo_state -> string -> (string list * THM) list -> 
                      (string list * THM) list -> repo_state
    
    (* Repository folder management *)
    val write_folder_header : repo_state -> repo_state
    val write_folder_entry : repo_state -> string -> repo_position -> repo_state
    val finalize_folder : repo_state -> repo_state
end;

(* ===================================================================== *)
(* CONVERSION FUNCTIONS SIGNATURES *)
(* ===================================================================== *)

signature PP_TO_SPADE_CONVERTER = sig
    
    (* Convert ProofPower objects to SPaDE format *)
    val pp_type_to_htype : TYPE -> htype
    val pp_term_to_hterm : TERM -> hterm
    val pp_thm_to_hsequent : THM -> hsequent
    
    (* Extract signature information from definitions *)
    val extract_signature : (string list * THM) -> (string * htype) list
    val extract_constraint : (string list * THM) -> hterm
    val classify_tag : string -> [`TYPE of int | `CONST of htype]
    
    (* Theory processing utilities *)
    val topological_sort : string list -> string list
    val gather_theory_extensions : string -> ((string * htype) list * hterm) list
    val gather_theory_axioms : string -> hterm list
end;

(* ===================================================================== *)
(* MAIN EXPORT ORCHESTRATION SIGNATURES *)
(* ===================================================================== *)

signature PROOFPOWER_EXPORTER = sig
    
    (* Top-level export functions *)
    val scrape_pp_theories : string -> string list -> unit
    val scrape_pp_db : string -> unit
    
    (* Theory processing functions *)
    val process_theory : repo_state -> string -> repo_state
    val process_theory_list : repo_state -> string list -> repo_state
    
    (* Utility functions *)
    val validate_theory_order : string list -> bool
    val compute_theory_dependencies : string list -> string list
    val estimate_repository_size : string list -> int
    
    (* Error handling *)
    exception ExportError of string
    exception TheoryNotFound of string
    exception InvalidTheoryOrder of string list
end;

(* ===================================================================== *)
(* COMBINED EXPORT INTERFACE *)
(* ===================================================================== *)

signature PP_SPADE_EXPORT = sig
    include PROOFPOWER_INTERFACE
    include SPADE_REPO_WRITER
    include PP_TO_SPADE_CONVERTER
    include PROOFPOWER_EXPORTER
end;