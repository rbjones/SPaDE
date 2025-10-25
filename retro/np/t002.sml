open_theory "hol";
force_new_theory "t002a";
new_parent "diffgeom";
declare_infix (300, "+⋎v");
declare_infix (300, "-⋎v");
declare_infix (310, "*⋎sv");
ⓈHOLCONST
│ $+⋎v $-⋎v : ℝ⋏3 → ℝ⋏3 → ℝ⋏3;
│ ~⋎v : ℝ⋏3 → ℝ⋏3;
│ $*⋎sv : ℝ → ℝ⋏3 → ℝ⋏3;
│ 0⋎v : ℝ⋏3;
│ d⋎v : ℝ⋏3 → ℝ
├──────
│ ∀ x y r⦁
│  	x +⋎v y = Plus⋎N x y ℝ⋏3⋎NVS
│ ∧	~⋎v x = Minus⋎N x ℝ⋏3⋎NVS
│ ∧	x -⋎v y = Subtract⋎N x y ℝ⋏3⋎NVS
│ ∧	r *⋎sv x = Scale⋎N r x ℝ⋏3⋎NVS
│ ∧	0⋎v =  0⋎N ℝ⋏3⋎NVS
│ ∧	d⋎v x = Norm⋎N x ℝ⋏3⋎NVS
■
declare_type_abbrev ("V", [], ⓣℝ⋏3⌝); 
declare_type_abbrev ("STATE⋎1", [], ⓣV → ℝ × V⌝); 
ⓈHOLCONST
│ State⋎1 : STATE⋎1 → BOOL
├──────
│ ∀ s ⦁ State⋎1 s ⇔
│	∀v⦁	let (mass, vel) = s v
│		in mass ≥ 0⋎R
│		∧ (mass = 0⋎R ⇒ vel = 0⋎v)
■
declare_type_abbrev ("UV⋎1", [], ⓣℝ → STATE⋎1⌝); 
ⓈHOLCONST
│ Uv⋎1 : UV⋎1 → BOOL
├──────
│ ∀ uv⦁ Uv⋎1 uv ⇔ ∀t⦁ State⋎1 (uv t)
■
declare_type_abbrev ("PARTICLE", [], ⓣℝ × (ℝ → V)⌝); 
declare_type_abbrev ("UV⋎2", [], ⓣPARTICLE LIST⌝);
ⓈHOLCONST
│ Conformant: UV⋎1 → UV⋎2 → BOOL
├──────
│ ∀ uv1 uv2⦁ Conformant uv1 uv2 ⇔
│ ∀t v m p⦁ uv1 t p = (m, v) ⇔
│	∃tr vh⦁ (m, tr) ∈⋎L uv2
│	∧ tr t = p
│	∧ VDeriv ℝ⋏3⋎NVS tr = vh
│	∧ vh t = v
■
ⓈHOLCONST
│ Pp : ('u → BOOL) → ('u → BOOL) → BOOL
├──────
│ ∀tuv puv ⦁ Pp tuv puv ⇔
│	  (∀uv ⦁ puv uv ⇒ tuv uv)
│	∧ (∃uv ⦁ puv uv)
│	∧ (∃uv ⦁ tuv uv ∧ ¬ puv uv) 
■
ⓈHOLCONST
│ Gc : ℝ
├──────
│ T
■
ⓈHOLCONST
│ Flds : ℝ × V → V
├──────
│ ∀ mass pos⦁
│	Flds (mass, pos) =
│	  if pos = 0⋎v
│	     then 0⋎v
│	     else
│		let d = d⋎v pos
│		in let mag = (Gc *⋎R mass) / (d ^⋎N 2)
│		    in ((mag / d) *⋎sv pos)
■
ⓈHOLCONST
│ Fldstot : PARTICLE LIST → ℝ → V → V
├──────
│ ∀ p lp t pos⦁
│	Fldstot [] t pos = 0⋎v
│ ∧	Fldstot (Cons p lp) t pos = (Flds (Fst p, (Snd p t) -⋎v pos))
│		+⋎v (Fldstot lp t pos)
■
ⓈHOLCONST
│ GAccHist : PARTICLE LIST → PARTICLE → (ℝ → V)
├──────
│ ∀ ma: ℝ; ta: ℝ → V; pl t⦁
│	GAccHist pl (ma, ta) t = Fldstot pl t (ta t)
■
ⓈHOLCONST
│ GAccHistl : PARTICLE LIST → (ℝ → V) LIST
├──────
│ ∀ lp⦁ GAccHistl lp = Map (GAccHist lp) lp
■
ⓈHOLCONST
│ AccHist : PARTICLE → (ℝ → V) → BOOL
├──────
│ ∀ p ah⦁  AccHist p ah = (VNthDeriv 2 ℝ⋏3⋎NVS (Snd p) = ah)
■
ⓈHOLCONST
│ AccHistpl : (PARTICLE × (ℝ → V))LIST → BOOL
├──────
│∀ pah pahl⦁  (AccHistpl []  ⇔ T)
│ ∧ (AccHistpl (Cons pah pahl)
│		 ⇔ AccHist (Fst pah) (Snd pah) ∧ (AccHistpl pahl))
■
ⓈHOLCONST
│ AccHistl : PARTICLE LIST → (ℝ → V) LIST → BOOL
├──────
│∀ pl al⦁ AccHistl pl al ⇔ AccHistpl (Combine pl al)
■
ⓈHOLCONST
│ Newtonian⋎2 : UV⋎2 → BOOL
├──────
│ ∀ uv2⦁ Newtonian⋎2 uv2 ⇔ AccHistl uv2 (GAccHistl uv2)
■
ⓈHOLCONST
│ Newtonian⋎1 : UV⋎1 → BOOL
├──────
│ ∀ uv1⦁ Newtonian⋎1 uv1 ⇔ 
│	∃ uv2⦁ Conformant uv1 uv2 ∧ Newtonian⋎2 uv2
■
new_conjecture (["Pp_Newtonian"], ⌜Pp (λw⦁T) Newtonian⌝);
ⓈHOLCONST
│ Rc : ℝ
├──────
│ T
■
output_theory{out_file="t002a.th.doc", theory="t002a"};
