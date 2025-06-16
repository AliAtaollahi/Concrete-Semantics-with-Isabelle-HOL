theory Programming_and_Proving
  imports Main
begin

(* 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
value "[a,b] @ [c,d]"

(* 2.2 *)

(* Define custom addition on nat *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)"

(* Associativity: (m + n) + p = m + (n + p) *)
lemma add_assoc: "add (add m n) p = add m (add n p)"
  by(induction m) (auto)

lemma add_right_zero: "add n 0 = n"
  by (induction n) simp_all
lemma add_suc [simp]: "add n (Suc m) = Suc (add n m)"
  by (induction n) simp_all
lemma add_comm [simp]: "add m n = add n m"
  by (induction m) (simp_all add: add_right_zero)

(* extra lemmas needed because we should have reverse assumptions *)

fun double :: "nat \<Rightarrow> nat" where
  "double 0       = 0" | 
  "double (Suc m) = Suc (Suc (double m))"

theorem double_eq_add: "double m = add m m"
  by (induction m) simp_all

(* 2.3 *)

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count []     x = 0" |
  "count (y#ys) x = (if x = y then Suc (count ys x) else count ys x)"

value "count []      (3::nat)"
value "count [1,2,1,3,1] (1::nat)"
value "count [True, False, True] True"

theorem count_le_length: "count xs x \<le> length xs"
  by (induct xs arbitrary: x) (simp_all add: le_SucI)

(* 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y#ys) x = y # snoc ys x"

value "snoc ([]::nat list) 42"
value "snoc ([1, 2, 3]::nat list) 4"
value "snoc ([]::bool list) True"
value "snoc ([False]::bool list) True"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) = snoc (reverse xs) x"

value "reverse ([1]::nat list)"
value "reverse ([1,2,3]::nat list)"
value "reverse [True, False, False]"

lemma reverse_snoc: "reverse (snoc xs x) = x # reverse xs"
  by (induct xs arbitrary: x) simp_all

theorem snoc_reverse: "reverse (reverse xs) = xs"
  by (induct xs) (simp_all add: reverse_snoc)

(* 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"

value "sum_upto 5"
value "sum_upto 10"

theorem sum_upto_formula: "sum_upto n = n * (n + 1) div 2"
  by (induct n) simp_all

(* 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l x r) = contents l @ [x] @ contents r"

value "contents (((Tip) :: nat tree))"
value "contents ((Node Tip 3 Tip) :: nat tree)"
value "contents ((Node (Node Tip 1 Tip) 2 (Node Tip 4 Tip)) :: nat tree)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l x r) = sum_tree l + x + sum_tree r"

value "sum_tree (((Tip) :: nat tree))"
value "sum_tree ((Node Tip 3 Tip) :: nat tree)"
value "sum_tree ((Node (Node Tip 1 Tip) 2 (Node Tip 4 Tip)) :: nat tree)"

theorem "sum_tree t = sum_list(contents t)"
  by (induct t) simp_all

(* 2.7 *)

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Tip x) = Tip x" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

value "mirror (((Tip 2) :: nat tree2))"
value "mirror ((Node (Tip 1) 3 (Tip 2)) :: nat tree2)"
value "mirror ((Node (Node (Tip 1) 2 (Tip 3)) 4 (Node (Tip 5) 6 (Tip 7))) :: nat tree2)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip x) = [x]" |
  "pre_order (Node l x r) =  [x] @ (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip x) = [x]" |
  "post_order (Node l x r) =  (post_order l) @ (post_order r) @ [x]"

value "pre_order ((Node (Node (Tip 1) 2 (Tip 3)) 4 (Node (Tip 5) 6 (Tip 7))) :: nat tree2)"
value "post_order ((Node (Node (Tip 1) 2 (Tip 3)) 4 (Node (Tip 5) 6 (Tip 7))) :: nat tree2)"

theorem "pre_order (mirror t) = rev (post_order t)"
  by (induct t) simp_all

(* 2.8 *)

fun intersperse :: " 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a (x # xs) = x # a # intersperse a xs"

value "intersperse 0 ([] :: nat list)"
value "intersperse 0 ([1,2,3] :: nat list)"

value "map Suc ([] :: nat list)"
value "map Suc [1,2,3] :: nat list"

theorem map_intersperse: "map f (intersperse a l) = intersperse (f a) (map f l)"
  by (induct l rule:intersperse.induct) simp_all

(* 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"

value "itadd 0 10"
value "itadd 3 10"

theorem "itadd m n = add m n"
  by (induct m arbitrary:n) (simp_all add: add_right_zero)

(* 2.10 *)

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + nodes l + nodes r"

value "nodes (Tip :: tree0)"
value "nodes (Node (Node Tip Tip) (Node Tip Tip) :: tree0)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

value "nodes (explode 2 ((Node Tip Tip) :: tree0))"

theorem explode_exponential: "nodes (explode n t) = 2^n * (nodes t + 1) - 1"
  by (induction n arbitrary:t) (simp_all add:algebra_simps)

(* 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x" |
  "eval (Const k) x = k" |
  "eval (Add p q) x = eval p x + eval q x" |
  "eval (Mult p q) x = eval p x * eval q x"

value "eval (Mult (Add (Const 2) Var) Var) 3"
value "eval (Add (Mult (Const 2) Var ) (Const 3)) i" 

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] y = 0" |
  "evalp (x # xs) y = x + y * evalp xs y"

value "evalp [4,2,-1,3] (1 :: int)"
value "evalp [4,2,-1,3] (2 :: int)"

fun vadd :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "vadd [] xs = xs" |
  "vadd xs [] = xs" |
  "vadd (x # xs) (y # ys) = (x + y) # vadd xs ys"

value "vsum ([] :: int list) [1,2,3]"
value "vsum [0,-1,2] [3,1]"

fun mult_dist :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mult_dist k [] = []" |
  "mult_dist k (x#xs) = k * x # mult_dist k xs"

value "mult_dist 3 ([]       :: int list)"
value "mult_dist 3 [1,2,3]"

fun vmult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "vmult [] xs = []" |
  "vmult (x#xs) ys = vadd (mult_dist x ys) (0 # vmult xs ys)"

value "vmult ([] :: int list) [1,2,3]"
value "vmult [1,2] [3,4]"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const k) = [k]" |
  "coeffs (Add p q) = vadd (coeffs p) (coeffs q)" |
  "coeffs (Mult p q) = vmult (coeffs p) (coeffs q)"

lemma evalp_vadd: "evalp (vadd xs ys) x = evalp xs x + evalp ys x"
  by (induct xs ys rule: vadd.induct) (simp_all add:algebra_simps)

lemma evalp_mult_dist: "evalp (mult_dist k xs) y = k * evalp xs y"
  by (induct xs arbitrary: k y) (simp_all add: distrib_left)

lemma evalp_vmult: "evalp (vmult xs ys) y = evalp xs y * evalp ys y"
  by (induct xs ys arbitrary:y rule: vmult.induct) (simp_all add:algebra_simps evalp_mult_dist evalp_vadd)

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
  by (induct e arbitrary: x) (simp_all add: evalp_vadd evalp_vmult)

end