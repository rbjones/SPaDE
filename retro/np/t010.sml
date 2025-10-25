infix 4 AND_OR_T;
infix 4 AND_OR;
open_theory "basic_hol";
set_pc "basic_hol";
val _ =	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["sqsubseteq2"], Value "⊑", Simple) ]
        end
handle _ => ();
val _ =	let open ReaderWriterSupport.PrettyNames;
	in add_new_symbols [ (["identical2"], Value "≡", Simple) ]
        end
handle _ => ();
signature RbjTactics1 = sig
val pc_canon: string -> CANON -> CANON;
val rule_canon: (THM -> THM) -> CANON;
val ⇒_T_canon: CANON;
val ⇔_FC_T: (THM list -> TACTIC) -> THM list -> TACTIC;
val all_⇒_intro_canon: CANON;
val abc_canon: CANON;
val abc_tac: THM list -> TACTIC;
val asm_abc_tac: THM list -> TACTIC;
val map_eq_sym_rule : THM -> THM;
val list_map_eq_sym_rule : THM list -> THM list;
val SYM_ASMS_T : (THM list -> TACTIC) -> TACTIC;
val split_pair_conv : TERM -> THM;
val split_pair_rewrite_tac : TERM list -> THM list -> TACTIC;
val map_uncurry_conv : CONV;
val map_uncurry_rule : THM -> THM;
val rule_asm_tac : TERM -> (THM -> THM) -> TACTIC;
val rule_nth_asm_tac : int -> (THM -> THM) -> TACTIC;
val try : ('a -> 'a) -> ('a -> 'a);
val ℝ_top_anf_tac : TACTIC;
val COND_CASES_T : TERM -> THM_TACTIC -> TACTIC;
val cond_cases_tac : TERM -> TACTIC;
val less_cases_conv : CONV;
val less_cases_rule : THM -> THM;
end; (* of signature RbjTactics1 *)
structure RbjTactics1 : RbjTactics1 = struct
fun pc_canon string canon = strip_∧_rule o (pc_rule string (list_∧_intro o canon));

fun rule_canon rule thm = [rule thm];

fun ⇒_T_canon thm =
	if is_⇒ ((snd o strip_∀) (concl thm))
	then [thm]
	else [⇒_intro ⌜T⌝ thm];

fun ⇔_FC_T tac thms = GET_ASMS_T (tac o (fc_rule (flat (map fc_⇔_canon thms))));

val all_⇒_intro_canon: CANON = rule_canon all_⇒_intro;

val abc_canon =
	REPEAT_CAN (
		simple_∀_rewrite_canon
		ORELSE_CAN (rule_canon undisch_rule)
		ORELSE_CAN ∧_rewrite_canon)
	THEN_CAN all_⇒_intro_canon
	THEN_CAN ⇒_T_canon;

fun abc_tac thml =
	let val thms = flat (map abc_canon thml)
	in REPEAT (accept_tac t_thm ORELSE (bc_tac thms))
	end;

fun asm_abc_tac thml (asms, conc) =
	abc_tac (thml @ (map asm_rule asms)) (asms, conc);
fun map_eq_sym_rule thm = conv_rule (ONCE_MAP_C eq_sym_conv) thm;
fun list_map_eq_sym_rule thms = map (fn th => map_eq_sym_rule th handle _=> th) thms;
fun SYM_ASMS_T tltt = GET_ASMS_T (tltt o list_map_eq_sym_rule);
fun split_pair_conv t = prove_rule [] ⌜ⓜt⌝ = (Fst ⓜt⌝, Snd ⓜt⌝)⌝;
fun split_pair_rewrite_tac tl thms =
	pure_once_rewrite_tac (map split_pair_conv tl)
	THEN TRY (pure_rewrite_tac thms);

local	val uncurry_thm = tac_proof (
		([], ⌜∀f⦁ Uncurry f = λp⦁ f (Fst p) (Snd p)⌝),
		rewrite_tac [ext_thm, uncurry_def]);
	val pair_lemma = nth 2 (strip_∧_rule pair_ops_def);
	val uc_conv = (simple_eq_match_conv1 uncurry_thm)
		THEN_C (λ_C ((RATOR_C β_conv) THEN_C β_conv));
in
	val map_uncurry_conv = MAP_C uc_conv THEN_C pure_rewrite_conv [pair_lemma]
end;

val map_uncurry_rule = conv_rule map_uncurry_conv;

fun rule_asm_tac term rule = DROP_ASM_T term (strip_asm_tac o rule);
fun rule_nth_asm_tac int rule = DROP_NTH_ASM_T int (strip_asm_tac o rule);

fun try f a = f a handle _ => a;
val ℝ_top_anf_tac = conv_tac (TOP_MAP_C ℝ_anf_conv);
fun COND_CASES_T x tt = CASES_T x (fn y => TRY (rewrite_tac [y]) THEN (tt y));
fun cond_cases_tac x = COND_CASES_T x strip_asm_tac;
local 
   fun less_suc_n_conv t =  
	let val (_, [m,sn]) = strip_app t;
	    val (_, [n,_]) = strip_app sn;
	in list_∀_elim [m, n] less_plus1_thm
	end;
   in fun less_cases_conv t = ((RIGHT_C plus1_conv) THEN_C less_suc_n_conv THEN_TRY_C (RIGHT_C less_cases_conv)) t
end;
val less_cases_rule = conv_rule less_cases_conv;
end; (* of structure RbjTactics1 *)
signature StripFail = sig
val check_asm_tac1 : THM -> TACTIC;
val strip_asm_tac1 : THM -> TACTIC;
val strip_asms_tac1 : THM list -> TACTIC;
val AND_OR_T : TACTIC * TACTIC -> TACTIC;
val AND_OR : TACTIC * TACTIC -> TACTIC;
val ∧_THEN_T1 : (THM -> TACTIC) -> (THM -> TACTIC);
val ∧_THEN1 : (THM -> TACTIC) -> (THM -> TACTIC);
val STRIP_THM_THEN1 : THM_TACTICAL;
val LIST_AND_OR_T : TACTIC list -> TACTIC;
val MAP_LIST_AND_OR_T : ('a -> TACTIC) -> 'a list -> TACTIC;
val MAP_LIST_AND_OR : ('a -> TACTIC) -> 'a list -> TACTIC;
end; (* of signature StripFail *)
structure StripFail : StripFail = struct
fun check_asm_tac1 (thm : THM) : TACTIC = (fn gl as (seqasms, conc) =>
	let	val t = concl thm;
	in	if t ~=$ conc
		then accept_tac thm
		else if is_t t
		then fail_tac
		else if is_f t
		then f_thm_tac thm
		else if is_¬ t
		then	let	val t' = dest_¬ t;
				fun aux (asm :: more) = (
					if t ~=$ asm
					then fail_tac
					else if asm ~=$ t'
					then accept_tac (¬_elim conc (asm_rule asm) thm)
					else if asm ~=$ conc
					then accept_tac (asm_rule asm)
					else aux more
				) | aux [] = asm_tac thm;
			in	aux seqasms
			end
		else	let	fun aux (asm :: more) = (
					if t ~=$ asm
					then fail_tac
					else if is_¬ asm andalso (dest_¬ asm) ~=$ t
					then accept_tac (¬_elim conc thm (asm_rule asm))
					else if asm ~=$ conc
					then accept_tac (asm_rule asm)
					else aux more
					) | aux [] = asm_tac thm;
			in	aux seqasms
			end
	end	gl
);
fun ((tac1 : TACTIC) AND_OR_T (tac2 : TACTIC)) : TACTIC = (fn gl =>
	let	val (fok, (sgs1, pf)) = (true, tac1 gl) handle (Fail _) => (false, id_tac gl)
	in	let val (sgs2pfs2) = (map tac2 sgs1);
		in	(flat (map fst sgs2pfs2),
			pf o map_shape (map (fn (sgs, pf) => (pf, length sgs))sgs2pfs2))
		end handle (Fail _) =>
			if fok then (sgs1, pf) else fail_tac gl
	end
);
val op AND_OR = op AND_OR_T;
fun ∧_THEN_T1 (ttac : THM -> TACTIC) : THM -> TACTIC = (fn thm => 
	let	val thm1 = ∧_left_elim thm;
		val thm2 = ∧_right_elim thm;
	in	ttac thm1 AND_OR ttac thm2
	end
	handle ex => divert ex "∧_left_elim" "∧_THEN1" 28032 
		[fn () => string_of_thm thm]
);
val ∧_THEN1 = ∧_THEN_T1;
val STRIP_THM_THEN1 : THM_TACTICAL = (fn ttac:THM_TACTIC => 
	fn thm :THM =>
	(FIRST_TTCL[CONV_THEN (current_ad_st_conv()),
		∧_THEN1, 
		∨_THEN, 
		SIMPLE_∃_THEN]
	ORELSE_TTCL
		FAIL_WITH_THEN "STRIP_THM_THEN1" 28003 
			[fn () => string_of_thm thm])
	ttac
	thm
);
fun LIST_AND_OR_T (tacs : TACTIC list) :  TACTIC = (fn gl =>
	(fold (op AND_OR) tacs fail_tac) gl
);
fun MAP_LIST_AND_OR_T (tacf : 'a -> TACTIC) (things : 'a list) : TACTIC = (
	LIST_AND_OR_T (map tacf things)
);
val MAP_LIST_AND_OR : ('a -> TACTIC) -> 'a list -> TACTIC = MAP_LIST_AND_OR_T;
val strip_asm_tac1 = REPEAT_TTCL STRIP_THM_THEN1 check_asm_tac1;
val strip_asms_tac1 = MAP_LIST_AND_OR strip_asm_tac1;
end; (* of structure StripFail *)
signature PreConsisProof = sig
val save_cs_∃_thm : THM -> THM;
(* Proof Context: 'savedthm_cs_∃_proof *)
val CombI_prove_∃_rule : string -> TERM -> THM;
val ∃_⇒_conv : CONV;
val prove_∃_⇒_conv : CONV;
val force_new_theory : string -> unit;
val force_new_pc : string -> unit;
val add_pc_thms : string -> THM list -> unit;
val add_pc_thms1 : string -> THM list -> unit;
val output_stats : string -> unit;
end; (* of signature PreConsisProof *)
structure PreConsisProof : PreConsisProof = struct
val lthy = get_current_theory_name ();
val _ = open_theory "basic_hol";
val _ = push_merge_pcs ["'propositions","'paired_abstractions"];
fun lget x = fst(hd x);
val _ = new_pc "build_predicates";
val _ = set_rw_eqn_cxt ((lget o get_rw_eqn_cxt) "'propositions" @
		(lget o get_rw_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_sc_eqn_cxt ((lget o get_sc_eqn_cxt) "'propositions" @
		(lget o get_sc_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_st_eqn_cxt ((lget o get_st_eqn_cxt) "'propositions" @
		(lget o get_st_eqn_cxt) "'paired_abstractions")
		"build_predicates";
val _ = set_rw_canons ((lget o get_rw_canons) "'propositions" @
		(lget o get_rw_canons) "'paired_abstractions")
		"build_predicates";
val strip_pair :TERM -> TERM list = strip_leaves dest_pair;
val full_strip_∧ : TERM -> TERM list = strip_leaves dest_∧;
local
	val ci = ⌜pp'TS:BOOL → BOOL⌝;
in
fun mark (tm:TERM):TERM = mk_app(ci,tm)
end;
val _ = delete_pc "build_predicates";
val _ = pop_pc();
val _ = open_theory lthy;
val ∃_⇒_conv : CONV = (
	let	val ∃_⇒_lemma = prove_rule[]
			⌜∀p q⦁ (∃f⦁q ⇒ p f) ⇔ (q ⇒ ∃f⦁p f)⌝;
	in	fn tm =>
		let	val (f, b) = dest_simple_∃ tm;
			val (q, pf) = dest_⇒ b;
			val p = mk_simple_λ(f, pf);
			val thm1 = list_∀_elim[p, q] ∃_⇒_lemma;
			val thm2 = conv_rule(LEFT_C(BINDER_C (RIGHT_C β_conv))) thm1;
			val thm3 = conv_rule(RIGHT_C(RIGHT_C(BINDER_C β_conv))) thm2;
			val thm4 = simple_eq_match_conv thm3 tm;
		in	thm4
		end
	end
);
val prove_∃_⇒_conv : CONV = (fn tm =>
	let	val thm1 = tac_proof (([], tm),
				REPEAT strip_tac
			THEN	conv_tac ∃_⇒_conv
			THEN	⇒_T discard_tac
			THEN	conv_tac basic_prove_∃_conv);
		val thm2 = ⇔_t_intro thm1;
	in	thm2
	end
);
fun force_new_theory name =
  let val _ = force_delete_theory name handle _ => ();
  in new_theory name
end;
fun force_new_pc name =
  let val _ = delete_pc name handle _ => ();
  in new_pc name
end;
fun add_pc_thms pc thms =
		(add_rw_thms thms pc;
		add_sc_thms thms pc;
 		add_st_thms thms pc);
fun add_pc_thms1 pc thms =
		(add_rw_thms thms pc;
		add_sc_thms thms pc);
val saved_cs_∃_thm = ref t_thm;
fun save_cs_∃_thm thm = (saved_cs_∃_thm := thm; thm);
fun savedthm_cs_∃_conv x =
	if x =$ (concl(!saved_cs_∃_thm))
	then (⇔_t_intro (!saved_cs_∃_thm)) handle _ => (* eq_ *) refl_conv x
	else (* eq_ *) refl_conv x;
val _ = force_new_pc "'prove_∃_⇒_conv";
val _ = set_cs_∃_convs [prove_∃_⇒_conv, ONCE_MAP_C (pure_once_rewrite_conv [let_def] THEN_C (MAP_C β_conv))] "'prove_∃_⇒_conv";
val _ = commit_pc "'prove_∃_⇒_conv";
val _ = force_new_pc "'savedthm_cs_∃_proof";
val _ = set_cs_∃_convs [prove_∃_⇒_conv, savedthm_cs_∃_conv] "'savedthm_cs_∃_proof";
val _ = set_pr_conv basic_prove_conv "'savedthm_cs_∃_proof";
val _ = set_pr_tac basic_prove_tac "'savedthm_cs_∃_proof";
val _ = commit_pc "'savedthm_cs_∃_proof";
local	val lthy = get_current_theory_name ();
	val _ = open_theory "combin";
	val CombI_def = get_spec ⌜CombI⌝;
	val _ = open_theory lthy
in
fun CombI_prove_∃_rule pc tm =
	let val tmthm = pc_rule pc basic_prove_∃_rule tm
	in save_cs_∃_thm (rewrite_rule [CombI_def] tmthm)
	end
end;
local fun format_stat (name, value) = "$" ^ name ^ "$ & " ^ (Int.toString value) ^ "\\\\\n";
in fun output_stats filename = 
	let val out_strm = open_out filename
	    and stats = get_stats();
	    val total = Int.toString (fold (fn ((s,i1),i2) => i1+i2) stats 0)
	    val	output_string = concat(map format_stat stats) ^ "\\hline\nTotal & " ^ total ^ "\\\\\\hline"
	in output (out_strm, "=TEX\nInference Rule & Count\\\\\\hline\n");
	   output (out_strm, output_string);
	   close_out out_strm
	end;
end;

end; (* of structure PreConsisProof *)
signature UnifyForwardChain = sig
val simple_⇒_unify_mp_rule1 : THM -> THM -> THM ;
val ⇒_unify_mp_rule1 : THM -> THM -> THM ;
val unify_forward_chain_rule : THM list -> THM list -> THM list;
val ufc_rule : THM list -> THM list -> THM list;
val UFC_T1 :
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_UFC_T1 :
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ASM_UFC_T1 : 
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_ASM_UFC_T1 : 
	(THM -> THM list) -> (THM list -> TACTIC) -> THM list -> TACTIC;
val UFC_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_UFC_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ASM_UFC_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_ASM_UFC_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_UFC_⇔_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ALL_ASM_UFC_⇔_T :
	(THM list -> TACTIC) -> THM list -> TACTIC;
val ufc_tac : THM list -> TACTIC;
val all_ufc_tac : THM list -> TACTIC;
val asm_ufc_tac : THM list -> TACTIC;
val all_asm_ufc_tac : THM list -> TACTIC;
val all_ufc_⇔_tac : THM list -> TACTIC;
val all_asm_ufc_⇔_tac : THM list -> TACTIC;
val all_ufc_⇔_rewrite_tac : THM list -> TACTIC;
val all_asm_ufc_⇔_rewrite_tac : THM list -> TACTIC;
end; (* of signature UnifyForwardChain *)
structure UnifyForwardChain : UnifyForwardChain = struct
val was_theory = get_current_theory_name ();
val _ = open_theory "basic_hol";
val _ = set_merge_pcs ["'propositions", "'simple_abstractions"];
open Resolution; open Unification; open StripFail; open RbjTactics1

fun simple_⇒_unify_mp_rule1 ith ath =
 let	val s1 = ⇒_elim ith ath;
 in
	s1
 end handle (Fail _) =>
	let
	val (iasms, iconc) = dest_thm ith;
	val (aasms, aconc) = dest_thm ath;
	fun ttys t =  map mk_vartype (term_tyvars t);
	fun ittys (asms, conc) =  (ttys conc) drop
		(fn x => present (op =:) x (list_union (op =:) (map ttys asms)));
	val iityvs = ittys (iasms, iconc);
	val aityvs = ittys (aasms, aconc);
	val (ivars, barei) = strip_∀ iconc;
	val (avars, barea) = strip_∀ aconc;
	val (ai, c) = dest_⇒ barei;
	val (aivars, bareai) = strip_∀ ai;
	val subs = new_subs 40;
	val ((ityi, ites) , (atyi, ates)) =
		term_unify subs [] [] (
			(bareai, ivars, iityvs),
			(barea, avars, aityvs));
	val _ = init_subs subs;
	fun laux [] t = t
	|   laux ((nt1, t1)::tl) t = if t1 =$ t then nt1 else laux tl t;
	val ites2 = map (laux ites) ivars;
	val ates2 = map (laux ates) avars;
	val ni = list_∀_elim ites2 (inst_type_rule ityi ith);
	val na = list_∀_elim ates2 (inst_type_rule atyi ath);
	val naithm = list_∀_intro aivars na;
	val othm = ⇒_elim ni naithm;
	val ccfrees = frees (concl othm);
	val cafrees = list_union (op =$) (map frees (asms othm));
	val bindvars = ccfrees drop (fn x => (present (op =$) x cafrees))
	in (list_∀_intro bindvars othm)
end;
val all_∀_uncurry_rule = conv_rule(TRY_C all_∀_uncurry_conv);

fun ⇒_unify_mp_rule1 (thm1 : THM) : THM -> THM = (
let	val thm1' = all_∀_uncurry_rule thm1;
	val r' = simple_⇒_unify_mp_rule1 thm1'
		handle complaint =>
		pass_on complaint "simple_⇒_unify_mp_rule1"
			"⇒_unify_mp_rule1";
in
	(fn (thm2 : THM) =>
	r' thm2
	handle complaint => reraise complaint "⇒_unify_mp_rule1")
end);
local
val ¬_convs = map
	(fn t => simple_eq_match_conv1
		(all_∀_intro (tac_proof(([], t), simple_taut_tac))))
	[⌜¬t ⇒ F ⇔ t⌝, ⌜t ⇒ F ⇔ ¬t⌝];
in
fun unify_forward_chain_rule (imps : THM list) (ants : THM list) : THM list = (
let	val imp_rules = mapfilter ⇒_unify_mp_rule1 imps;
	fun aux1 acc _ [] = (acc
	) | aux1 acc (i :: il) (al as (a :: _)) = (
		(let val res = i a
		in
		if concl res =$ mk_f
		then [res]
		else
		(aux1 (res::acc) il al)
		end)
		handle Fail _ => aux1 acc il al
	) | aux1 acc [] (_ :: al) = (aux1 acc imp_rules al
	);
	fun aux2 thm = (
		case dest_term (concl thm) of
			D∀ (x, b) => (
				let val th = aux2 (asm_rule b);
				in ∀_intro x (prove_asm_rule (∀_elim x thm) th)
				end
		) |	D⇒ (a, b) => (
				(conv_rule(FIRST_C ¬_convs) thm)
				handle Fail _ =>
				let val th = aux2 (asm_rule b);
				in ⇒_intro a (prove_asm_rule(undisch_rule thm) th)
				end
		) |	_ => fail "" 99999 []
	);
	fun aux3 th = aux2 th handle Fail _ => th;
in	map aux3 (aux1 [] imp_rules ants)
end);
end;

val ufc_rule : THM list -> THM list -> THM list = unify_forward_chain_rule;

fun UFC_T1
	(can : THM -> THM list)
	(ttac : THM list -> TACTIC)
	(thms : THM list)
	: TACTIC = (fn gl as (asms, _) =>
	let	val asmthms = map asm_rule asms;
	in	ttac(ufc_rule(flat(map can thms)) asmthms) gl
	end
);
fun ASM_UFC_T1
	(can : THM -> THM list)
	(ttac : THM list -> TACTIC)
	(thms : THM list)
	: TACTIC = (fn gl as (asms, _) =>
	let	val asmthms = map asm_rule asms;
	in	ttac(ufc_rule(flat(map can (thms@asmthms))) asmthms) gl
	end
);

val UFC_T = UFC_T1 fc_canon;
val ASM_UFC_T = ASM_UFC_T1 fc_canon;

val ufc_tac : THM list -> TACTIC = UFC_T strip_asms_tac1;
val asm_ufc_tac : THM list -> TACTIC = ASM_UFC_T strip_asms_tac1;

fun ALL_UFC_T1 (can : CANON) (ttac : THM list -> TACTIC) (ths : THM list) : TACTIC = (
	let	fun aux1 acc [] = acc
		|   aux1 (imps, others) (th :: more) = (
			if is_⇒ (snd(strip_∀(concl th)))
			then aux1 (th :: imps, others) more
			else aux1 (imps, th :: others) more
		);
		fun aux2 acc imps = (
			UFC_T1 id_canon (fn thl =>
				let	val (imps, others) = aux1 ([], acc) thl;
				in	if	is_nil imps
					then	ttac others
					else	aux2 others imps
				end
			) imps
		);
		val ths' = flat (map can ths);
	in	aux2 [] (ths' drop (not o is_⇒ o snd o strip_∀ o concl))
	end
);
val ALL_UFC_T : (THM list -> TACTIC) -> THM list -> TACTIC = ALL_UFC_T1 fc_canon;

fun ALL_ASM_UFC_T1 (can : CANON) (ttac : THM list -> TACTIC) (thms : THM list) : TACTIC = (
	GET_ASMS_T (fn asm_thms => ALL_UFC_T1 can ttac (thms @ asm_thms)));
fun ALL_ASM_UFC_T (ttac : THM list -> TACTIC) (ths : THM list) : TACTIC = (
	GET_ASMS_T (fn thl => ALL_UFC_T ttac (thl @ ths)));

val all_ufc_tac : THM list -> TACTIC = ALL_UFC_T strip_asms_tac1;
val all_asm_ufc_tac : THM list -> TACTIC = ALL_ASM_UFC_T strip_asms_tac1;

val ALL_UFC_⇔_T = ALL_UFC_T1 fc_⇔_canon;
val ALL_ASM_UFC_⇔_T = ALL_ASM_UFC_T1 fc_⇔_canon;

val all_ufc_⇔_tac = ALL_UFC_⇔_T strip_asms_tac1;
val all_asm_ufc_⇔_tac = ALL_ASM_UFC_⇔_T strip_asms_tac1;

val all_ufc_⇔_rewrite_tac = ALL_UFC_⇔_T rewrite_tac;
val all_asm_ufc_⇔_rewrite_tac = ALL_ASM_UFC_⇔_T rewrite_tac;
end; (* of structure UnifyForwardChain *)
signature ParseComb = sig
exception parse_fail of int;

type 'a ptree;
type 'a pt_pack;
type 'a parser = 'a pt_pack -> 'a list -> 'a ptree * 'a list;

val alt_parse: 'a parser list -> 'a parser;
val seq_parse: 'a parser list -> 'a parser; 
val opt_parse: 'a parser -> 'a parser;  
val star_parse: 'a parser -> 'a parser;  
val plus_parse: 'a parser -> 'a parser; 
end; (* of signature ParseComb *)
structure ParseComb:ParseComb = struct

exception parse_fail of int;

datatype 'a tree = MkTree of 'a * 'a tree list;

type 'a ptree = int * 'a tree;

type 'a pt_pack = {	mk_plit:'a -> 'a ptree,
			mk_plist: 'a ptree list -> 'a ptree,
			mk_palt: int * 'a ptree -> 'a ptree,
			mk_popt: 'a ptree OPT -> 'a ptree};

type 'a parser = 'a pt_pack -> 'a list -> 'a ptree * 'a list;

datatype 'a pttag = Ptint of int | Ptlit of 'a | Ptnone; 

fun mk_ptp (mk_tree: ('a pttag) * 'b list -> 'b) = {
	mk_plit = fn l => mk_tree (Ptlit l, []),
	mk_plist = fn ptl => mk_tree (Ptnone, ptl),
	mk_palt = fn (i, pt) => mk_tree (Ptint i, [pt]),
	mk_popt = fn pto => mk_tree (Ptnone, (fn Nil => [] | Value pt => [mk_tree (Ptnone, [pt])])pto ) 
};

fun alt_parse (pl:'a parser list) (ptp as {mk_palt, ...}: 'a pt_pack) (li:'a list) =
	let fun aux (pl as (hp::tpl)) n j = (let val (pt, rli) = hp ptp li in (mk_palt (n, pt), rli) end
			handle parse_fail k => aux tpl (n+1) (if j < k then j else k))
	    |   aux [] n i = raise parse_fail i
	in aux pl 0 (length li)
	end;

fun seq_parse pl (ptp as {mk_plist, ...}:'a pt_pack) li =
	let fun aux (p, (ptl, li)) = let val (npt, rli) = p ptp li in (npt::ptl, rli) end
	    val (ptl, nli) = revfold aux pl ([], li)
	in (mk_plist (rev ptl), nli)
	end;

fun opt_parse p (ptp as {mk_popt, ...}:'a pt_pack) li =
	let val (pt, nli) = p ptp li
	in (mk_popt (Value pt), nli)
	end handle parse_fail i => (mk_popt Nil, li);

fun star_parse (p:'a parser) (ptp as {mk_plist, ...}:'a pt_pack) li =
	let	fun aux1 li =	let val (pt, rli) = p ptp li
				in ([pt], rli)
				end handle parse_fail i => ([], li)
		fun aux2 li =
			let val (ptl, rli) = aux1 li
			in	case ptl of
					[] => ([], rli)
				|	ptl =>	let val (ptl2, sli) = aux2 rli
					in (ptl @ ptl2, sli)
					end
			end
	    val (ptl, nli) = aux2 li
	in (mk_plist (rev ptl), nli)
	end;

fun plus_parse (p:'a parser) (ptp as {mk_plist, ...}:'a pt_pack) li =
	let	fun aux1 li =	let val (pt, rli) = p ptp li
				in ([pt], rli)
				end handle parse_fail i => ([], li)
		fun aux2 li =
			let val (ptl, rli) = aux1 li
			in	case ptl of
					[] => ([], rli)
				|	ptl =>	let val (ptl2, sli) = aux2 rli
					in (ptl @ ptl2, sli)
					end
			end
	    val (ptl, nli) = aux2 li
	in (mk_plist (rev ptl), nli)
	end;

end; (* of structure ParseComb *)
signature Grammar = sig
 
end; (* of signature Grammar *)
signature Trawling = sig
datatype THMDET = Spec of TERM | Thm of (string * string);
val on_conc : (TERM -> 'a) -> 'a;
val on_asms : (TERM list -> 'a) -> 'a;
val rew_thms : TERM -> ((int * THMDET) * THM) list;
val rew_specs : TERM -> ((int * THMDET) * THM) list;
val bc_thms : TERM -> ((int * THMDET) * THM) list;
val fc_thms : TERM list -> ((int * THMDET) * THM) list;
val all_fc_thms : TERM list -> ((int * THMDET) * THM) list;
val todo : unit -> {bc: int, fc: int, rw: int};
val td_thml : THMDET list -> THM list;
end; (* of signature Trawling *)
structure Trawling : Trawling = struct

val avoid_theories = ref ["min", "log", "misc", "sets", "combin", "pair", "list"];
val avoid_constants = ref [""];
val avoid_specs: string list ref = ref [""];

datatype THMDET =
		Spec of TERM
	|	Thm of (string * string);

fun is_defined_constant s =
	let val theoryname = get_const_theory s;
	    val defn = get_defn theoryname s
	in true
	end
	handle _ => false;

fun defined_consts t =
	let val consts = term_consts t
	in filter
		(fn x => not ((fst x) mem !avoid_constants)
		andalso is_defined_constant (fst x))
	   consts
	end;

fun defined_const_names t = map fst (defined_consts t);

fun on_conc f = f (snd (top_goal()));

fun on_asms f =
	let val (asms, concl) = top_goal()
	in f asms
	end;

fun on_goal f =
	let val (asms, concl) = top_goal()
	in  flat(map f (concl :: asms))
	end;

fun term_const_specs t =
	let fun gs (s,t) =
		let val c = mk_const (s,t)
		in (if	s mem !avoid_specs orelse
			(get_const_theory s) mem !avoid_theories
		   then []
		   else [(Spec c, get_spec c)]) handle _ => []
		end
	in flat (map gs (term_consts t))
	end;

fun const_theories t = list_cup (map (fn x => [get_const_theory x]) (defined_const_names t));

fun ancestor_theories t = filter (fn x => not (x mem !avoid_theories)) (get_ancestors t);

fun thy_thms t = map (fn (s,thm) => (Thm(t, hd s), thm)) (get_thms t);

fun const_thms t = flat(map thy_thms (const_theories t));

fun ancestor_thms t = flat(map thy_thms (ancestor_theories t));

fun rewriting_thm t thm =
	let val t' = pure_once_rewrite_conv [thm] t
	in true
	end handle _ => false;

local open RbjTactics1 in
fun srewriting_thm t thm = rewriting_thm t (map_eq_sym_rule thm) handle _ => false;
end;

fun fc_thm ts thm =
	let val thms = fc_rule (fc_canon thm) (map asm_rule ts)
	in (fn [] => false | _ => true) thms
	end handle _ => false;

fun all_fc_thm ts thm =
	let val (gl, pr) = all_fc_tac [thm] (ts, ⌜F⌝)
	in if length gl = 1 andalso length (fst (hd gl)) = length ts
		then false else true
	end handle _ => false;

fun bc_thm c thm =
	let val (gl, pr) = bc_tac [thm] ([], c)
	in if length gl = 1 andalso (snd (hd gl)) =$ c
		then false else true
	end handle _ => false;

fun numthms n [] = []
|   numthms n ((thmdets, thm)::t) = ((n, thmdets), thm):: (numthms (n+1) t);

fun rew_specs t =
	let val thms = term_const_specs t
	in numthms 1 (filter ((rewriting_thm t) o snd) thms)
	end;

fun terml_const_specs tl = flat (map term_const_specs tl);

fun fc_specs ts =
	let val thms = terml_const_specs ts
	in numthms 1 (filter ((fc_thm ts) o snd) thms)
	end;

fun bc_specs t =
	let val thms = term_const_specs t
	in numthms 1 (filter ((bc_thm t) o snd) thms)
	end;

fun rew_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((rewriting_thm t) o snd) thms)
	end;

fun srew_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((srewriting_thm t) o snd) thms)
	end;

fun fc_thms tl =
	let val thms = (ancestor_thms "-") @ (terml_const_specs tl)
	in numthms 1 (filter ((fc_thm tl) o snd) thms)
	end;

fun all_fc_thms tl =
	let val thms = (ancestor_thms "-") @ (terml_const_specs tl)
	in numthms 1 (filter ((all_fc_thm tl) o snd) thms)
	end;

fun bc_thms t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (filter ((bc_thm t) o snd) thms)
	end;

fun rew_thms2 t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (flat (map (fn (sl, th) =>
		[(sl, (th, (snd o dest_eq)(concl (pure_once_rewrite_conv [th] t))))]
		handle _ => []) thms))
	end;

fun rew_thms3 t =
	let val thms = (ancestor_thms "-") @ (term_const_specs t)
	in numthms 1 (flat (map (fn (sl, th) =>
		[(sl, (snd o dest_eq)(concl (pure_once_rewrite_conv [th] t)))]
		handle _ => []) thms))
	end;

fun const_rewrite_conv t =
	let val thms = map snd (rew_thms t)
	in rewrite_conv thms t
	end;

fun with_conc_thms f =
	let fun ff t = f (map snd (rew_thms t))
	in on_conc ff
	end;

fun with_conc_specs f =
	let fun ff t = f (map snd (rew_specs t))
	in on_conc ff
	end;

fun td_thm (Thm (thyn, thmn)) = get_thm thyn thmn
|   td_thm (Spec s) = get_spec s;

fun td_thml tdl = map td_thm tdl;

fun numl2tdl tdsl nl =
 map (fn chose => (snd o fst o chose) tdsl) (map (fn n=> nth (n-1)) nl);

fun todo () =
	let val rw = length (on_conc rew_thms)
	    val bc = length (on_conc bc_thms)
	    val fc = length (on_asms fc_thms)
	in {rw = rw, bc = bc, fc = fc}
	end;
end; (* of structure Trawling *)
fun lfoldl f a [] = a
|  lfoldl f a (h::t) = lfoldl f (f (a, h)) t;

fun lfoldr f a [] = a
|  lfoldr f a (h::t) = f (a, (lfoldr f h t));

fun list_s_enter [] d = d
|   list_s_enter ((s,v)::t) d = list_s_enter t (s_enter s v d); 

fun list_to_sdict l = list_s_enter l initial_s_dict;

fun list_pos e [] = 0
|   list_pos e (h::t) =
	if h = e
	then 1
	else	let val p = list_pos e t 
		in if p = 0 then 0 else p+1
		end;

val strip_→_type = strip_spine_right dest_→_type;

fun list_mk_×_type (h::t) = lfoldr mk_×_type h t;

fun match_mk_app (f, a) = mk_app(f, a) handle _ => ⌜ⓜf⌝ ⓜa⌝⌝;

fun list_match_mk_app (f, al) = lfoldl match_mk_app f al;

fun mk_tree_type ty = mk_ctype ("TREE", [ty]);

fun mk_tree t tl =
	let val tt = type_of t
	in mk_app (
		mk_const ("MkTree", mk_→_type (mk_×_type (tt, mk_ctype("LIST", [tt])), mk_tree_type tt)),
		tl)
	end;

fun dest_tree tr = dest_app tr;

fun list_mk_tree t tl = mk_tree t (mk_list tl);

fun dest_tree_list tr = let val (t, l) = dest_tree tr in (t, dest_list l) end;
fun gen_type_map cf vf ty =
	let fun aux (Vartype v) = vf v
	|       aux (Ctype (s, tl)) = cf s ((map (aux o dest_simple_type)) tl)
	in aux (dest_simple_type ty)
	end;

local fun front_last [e] = ([], e)
      |   front_last (f::t) = 
	   let val (f2, l) = front_last t
	   in (f::f2, l)
	   end
in fun front x = let val (f,l) = front_last x in f end
   fun last x = let val (f,l) = front_last x in l end
   fun right_rotate_list [] = []
   |   right_rotate_list [e] = [e]
   |   right_rotate_list x = let val (f,l) = front_last x in l :: f end
   fun left_rotate_list [] = []
   |   left_rotate_list [e] = [e]
   |   left_rotate_list (h::t) = t @ [h]
end;
infix symdiff;

fun x symdiff y = (x diff y) cup (y diff x);

fun dest_enum l =
	(fn DEnumSet els => els
	|  D∅ t => []) (dest_term l);

fun enum_eq_sdiff t =
	let val DEq (lhs, rhs) = dest_term t
	in (dest_enum lhs) symdiff (dest_enum rhs)
	end;

fun false_enum_eq_conv t =
	let val (dt :: _) = enum_eq_sdiff t
	in 
		tac_proof(([], ⌜ⓜt⌝ ⇔ F⌝),
			rewrite_tac [sets_ext_clauses]
			THEN ¬_in_tac
			THEN ∃_tac dt THEN prove_tac[])
	end handle _ => fail_conv t;

val false_enum_eq_tac = conv_tac (MAP_C false_enum_eq_conv); 
(new_error_message {id= 7044, text = "Cannot match ?0 and ?1\
\" }; new_error_message {id= 7045, text = "?0 is not of the form `Γ ⊢ ∀ x1 ... xn ⦁ u ⇒ v`\
\" }; new_error_message {id= 7044, text = "Cannot match ?0 and ?1\
\" }; new_error_message {id= 7045, text = "?0 is not of the form `Γ ⊢ ∀ x1 ... xn ⦁ u ⇒ v`" });
