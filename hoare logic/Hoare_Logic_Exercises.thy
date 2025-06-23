theory Hoare_Logic_Exercises
  imports "Hybrid-Verification.Hybrid_Verification"
begin

dataspace basic_programs = 
  constants 
    N :: int
    growing :: bool
  assumes 
    Nge0: "0 < N" 
    and growing_on: "growing"
  variables 
    x :: int
    y :: int
    z :: int
    name :: string
    stdout :: string

context basic_programs
begin


subsection ‹ Skip ›

lemma "H{0 ≤ x + y} skip {0 ≤ x + y}"
  by (simp add: hoare_skip)


subsection ‹ Abort ›

lemma "H{True} abort {0 ≤ x + y}"
  by (simp add: hoare_abort)


subsection ‹ Assignments ›

lemma "H{stdout = ''''} stdout ::= ''Hello World'' {stdout = ''Hello World''}"
  by (rule hoare_assignI, expr_simp)

lemma "H{True} x ::= 20 {x = 20}"
  by (rule hoare_assignI, expr_simp)

lemma "H{0 ≤ x} x ::= x + 1 {1 ≤ x}"
  by (rule hoare_assignI, expr_simp)

lemma "H{0 ≤ x} x ::= - x {x ≤ 0}"
  by (rule hoare_assignI, expr_simp)


subsection ‹ Composition ›

lemma "H{True} x ::= 4; y ::= 2 {x = 4 ∧ y = 2}"
  by symbolic_exec

lemma "H{z > 0} x ::= z; y ::= x {x > 0 ∧ y > 0}"
  by symbolic_exec

lemma "
H{x < y}
  z ::= x;
  x ::= y;
  y ::= z
{y < x}"
  by symbolic_exec


subsection ‹ Conditionals ›

lemma "H{0 ≤ x} IF x > 0 THEN x ::= -x ELSE x ::= x {x ≤ 0}"
  apply (rule hoare_if_then_else)
  apply (rule hoare_assignI)
  apply (expr_simp)
  apply (rule hoare_assignI)
  apply (expr_simp)
  done

lemma "H{True} IF N > 0 THEN x ::= N ELSE x ::= 2 * N {x > 0}"
  apply (rule hoare_if_then_else)
  apply (rule hoare_assignI)
  using Nge0 apply (expr_simp)
  apply (rule hoare_assignI)
  using Nge0 apply (expr_simp)
  done

lemma "H{True} x ::= 0; IF growing THEN x ::= x + 1 ELSE x ::= x - 1 {0 ≤ x}"
  apply (symbolic_exec)
  using growing_on apply (expr_simp)
  done

subsection ‹ While loops ›

lemma "H{N - x ≥ 0} (WHILE x < N DO x ::= x + 1 INV (N - x ≥ 0)) {x ≥ N ∧ N - x ≥ 0}"
proof (rule hoare_whileI)
  show "H{N - x ≥ 0 ∧ x < N} x ::= x + 1 {N - x ≥ 0}"
    by (hoare_wp_auto)
next
  show "`N - x ≥ 0 ⟶ N - x ≥ 0`"
    by expr_auto
next
  show "`N - x ≥ 0 ∧ ¬(x < N) ⟶ x ≥ N ∧ N - x ≥ 0`"
    by expr_auto
qed


lemma "
H{True} 
  x ::= 0; y ::= N;
  (WHILE x < N DO
    (x ::= x + 1;
    y ::= N - x)
  INV (x + y = N ∧ x ≤ N ∧ y ≥ 0))
{x = N}"
  apply (symbolic_exec)
  apply (rule hoare_whileI)
  apply (symbolic_exec)
  apply (expr_simp)
  using Nge0 apply auto[1]
  apply (expr_simp)
  done

(*
  apply (rule hoare_kcomp [where R="(x=0 ∧ y=N)⇧e"])
  apply (rule hoare_kcomp [where R="(x=0)⇧e"])
  apply (rule hoare_assignI)  
  apply expr_simp
  apply (rule hoare_assignI)  
  apply expr_simp
  apply (rule hoare_whileI)
  apply symbolic_exec
  apply expr_simp
  using Nge0 apply auto[1]
  apply expr_simp
  done
*)


lemma "
H{True} 
  x ::= 0;
  WHILE x < N DO
    x ::= x + 1
{x = N}"
  apply symbolic_exec
  apply (rule hoare_while_nannotI [where I="(x≤N)⇧e"])
  apply symbolic_exec
  using Nge0 apply fastforce
  apply expr_simp
  done
  
subsection ‹ Match ›

lemma "
H{name = ''Afrodita''} 
  CASE name OF 
    ''Afrodita'' ⇒ (stdout ::= ''Godess of beauty'')
    | ''Ares'' ⇒ (stdout ::= ''God of war'')
    | ''Poseidon'' ⇒ (stdout ::= ''God of the sea'')
{stdout = ''Godess of beauty''}"
  apply (rule hoare_match)
  apply wlp_full
  apply expr_simp
  apply (simp add: fbox_def assigns_def)
  done


subsection ‹ Tests ›

lemma "H{True} ¿x≥1? {x ≥ 1}"
  apply wlp_full
  done

lemma "H{x ≥ 0} ¿x≤-1? {False}"
  apply wlp_full
  done

lemma "H{x ≥ 0} ¿x≤-1? {y = 30}"
  apply wlp_full
  done


subsection ‹ Nondeterministic choice ›

lemma "H{0 ≤ x} x ::= x + 1 ⊓ y ::= x + 1 {0 ≤ x ∨ 1 ≤ x}"
  apply (rule hoare_choice)
  apply (rule hoare_assignI)
  apply expr_simp
  apply (rule hoare_assignI)
  apply expr_simp
  done

lemma "H{0 ≤ x} x ::= x + 1 ; (x ::= x + 1 ⊓ y ::= x + 1) {1 ≤ x}"
  apply symbolic_exec
  done

lemma "H{0 ≤ x} x ::= x + 1 ; (¿2 ≤ x? ; x ::= x - 1 ⊓ ¿∀z::int≥1. 1 ≤ y? ; x ::= y) {1 ≤ x}"
  apply wlp_full
  apply expr_auto
  done


subsection ‹ Nonderterministic iteration (or finite iteration) ›

lemma "H{x = y} LOOP x ::= x + 1 INV (y ≤ x) {y ≤ x}"
  apply wlp_full
  done

lemma "H{0 ≤ x} x ::= x + 1 ; LOOP x ::= x + 1 INV (1 ≤ x) {1 ≤ x}"
  apply wlp_full
  done

lemma "
  H{0 ≤ x ∧ 1 ≤ y} 
    x ::= x + 1 ; 
    ((LOOP x ::= x + 1 INV (1 ≤ x) 
      ⊓ y ::= x + 1
    ); x ::= y) 
  {1 ≤ x}"
  apply (rule hoare_kcomp [where R="(1 ≤ x ∧ 1 ≤ y)⇧e"])
  apply (rule hoare_assignI) 
  apply expr_auto
  apply (rule hoare_bwd_assign)
  apply (rule hoare_choice)
  apply (subst change_loopI[where I="(1 ≤ x ∧ 1 ≤ y)⇧e"])
  apply (rule hoare_loopI)
  apply (rule hoare_assignI)
  apply expr_auto
  apply expr_auto
  apply expr_auto
  apply (rule hoare_assignI)
  apply expr_auto
  done

(*
  you can use intro_loops instead hoare_loopI
*)

subsection ‹ Nondeterministic assignment ›

lemma "H{True} x ::= ? {∃k. x = k}"
  apply wlp_full
  done

lemma "H{x ≥ 0} x ::= x + 1 ; x ::= ? ; ¿x≥1? {x ≥ 1}"
  apply wlp_full
  done

end (* context basic_programs *)



end