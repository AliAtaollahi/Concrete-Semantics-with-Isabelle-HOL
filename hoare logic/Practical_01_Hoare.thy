section ‹ Practical 1: Hoare Logic ›

theory Practical_01_Hoare
  imports "Hybrid-Verification.Hybrid_Verification"
begin

subsection ‹ Preliminaries ›

notation undefined ("???")

alphabet state =
  x :: int
  y :: int
  q :: int
  r :: int

subsection ‹ Demonstration ›

text ‹ Hoare logic proofs require us to use @{method rule} to apply the introduction laws,
  @{method subst_eval'} to evaluated substitutions, and the usual proof methods to verify
  any proof obligations that arise. 

  Below we give a small example:
›

lemma d1: "H{x = 1} x ::= x + 1 {x = 2}"
  apply assign ― ‹ First, we apply the assignment law, yielding a conditional predicate ›
  apply (subst_eval') ― ‹ Second, we evaluate the substitution ›
  apply simp ― ‹ Finally, we use the simplifier to discharge the remaining subgoal ›
  done

text ‹ We can also express this as an Isar proof, to present the explicit reasoning: ›

lemma d1': "H{x = 1} x ::= x + 1 {x = 2}"
proof -
  ― ‹ First we formulate the main proof obligation required for the assignment. The backticks are
       use to denote a tautology -- the assertion should hold for any given state. ›
  have 1: "`x = 1 ⟶ (x = 2)⟦x + 1/x⟧`"
    by (subst_eval', simp)
  ― ‹ Second, we use the proof obligation as input to the assignment law, which completes the proof. ›
  thus ?thesis
    by assign
qed

text ‹ The next example will be done during the practical, to explain the sequential composition
  laws. ›

lemma d2: "H{x = X} y ::= x; x ::= x + x {x = 2 * X ∧ y = X}"
  apply (sequence "x = X ∧ y = X")
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  done

subsection ‹ Exercises ›

text ‹ Q1. Use the assignment method (@{method assign}) to attempt proof of the following Hoare triples 
  from the lecture. ›

lemma a1: "H{x = 1} x ::= 2 * x {x ≥ 1}"
  apply assign
  apply (subst_eval', simp)
  done

lemma a2: "H{x > 1} x ::= 2 * x {x > 1}"
  apply assign
  apply (subst_eval', simp)
  done

lemma a3: "H{x = 1} x ::= x + x {x = 2}"
  apply assign
  apply (subst_eval', simp)
  done

lemma a4: "H{x > N} x ::= x + 1 {x > N}"
  apply assign
  apply (subst_eval', simp)
  done

text ‹ Q2. Give a proof of the following Hoare triple, which we considered in the lecture,
  using the conditional method (@{method sequence}). ›

lemma a5: "H{True} IF x ≥ y THEN r ::= x ELSE r ::= y {r = max x y}"
  apply (if_then_else)
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  done


text ‹ Q3. Write a partial correctness specification that is valid if the command C has the
  effect of multiplying the values of x and y together and storing the result in x . ›

lemma a6: "H {λs. s x = x⇩o ∧ s y = y⇩o} (x ::= x * y)  {λs. s x = x⇩o * y⇩o}"
  oops


text ‹ Now, fill in a command @{term C} and use the assignment law to prove that the triple is valid. ›

text ‹ Q4. Prove the following Hoare triples, which we considered in the lecture, using the
  sequential composition method (@{method sequence}). If the simplifier cannot solve a proof 
  obligation, try to apply @{method expr_auto} followed by sledgehammer. ›

(* I changed post-condition *)
lemma a7: "H{x > 0} x ::= x + 1 ; x ::= x * x {x > 1}"
  apply (sequence "x > 1")
  apply assign
  apply (subst_eval', simp)
  apply expr_auto
  by (metis (lifting) SEXP_def fbox_assigns less_1_mult state.simps(1,6) subst_SEXP)

lemma a8: "H{2 * x = y} x ::= x + 1 ; y ::= y + 2 {2 * x = y}"
  apply (sequence "2 * x = y + 2")
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  done

text ‹ Q5. Is the following specification valid? If not, why not? ›

lemma a9: "H{x = X ∧ y = Y} x ::= y; y ::= x {y = X ∧ x = Y}"
  apply (sequence "x = Y ∧ y = Y")
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  apply expr_auto (* just when we have x = y, this is true*)
  oops

text ‹ If so, prove it. If not, give the circumstances in which it fails. You can do the latter
  with a Hoare triple that selects specific values in the precondition. ›

text ‹ Q6. Is the following specification valid? ›

lemma a10: "H{x = X ∧ y = Y} x ::= x + y; y ::= x - y; x ::= x - y {y = X ∧ x = Y}"
  apply (sequence "x = X + Y ∧ y = X")
  apply (sequence "x = X + Y ∧ y = Y")
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  done

text ‹ If so, prove it. If not, give the circumstances in which it fails. You can do the latter
  with a Hoare triple that selects specific values in the precondition. ›

text ‹ Q7. Show in detail a proof of the following Hoare triple. ›

lemma a11: "H{ x = r + (y * q) } r ::= r - y; q ::= q + 1 { x = r + (y * q) }"
  apply (sequence "x = r - y + (y * q)")
  apply assign
  apply (subst_eval', simp)
  apply assign
  apply (subst_eval', simp)
  oops

end