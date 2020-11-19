theory "prog-prove"
imports Main
begin
  fun conj :: "bool => bool => bool"
  where
  "conj True True = True"
| "conj _ _ = False"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

thm add_02

  term "a = True"
  term "b = -a"

  value "conj a b"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []"
| "rev (Cons x xs) = rev xs @ [x]"

lemma rev_works: "rev [1,2,3,4] = [4,3,2,1]"
  apply(auto)
  done

lemma rev_end [simp]: "rev (xs @ [y]) = y # rev xs"
  apply(induction xs)
   apply(auto)
  done

lemma rev_rev [simp]: "rev (rev xs) = xs"
  apply(induction xs)
   apply(auto)
  done

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

lemma add_one [simp]: "add x (Suc y) = Suc(add x y)"
  apply(induction x)
   apply(auto)
  done

lemma add_comm [simp]: "add x y = add y x"
  apply(induction x)
   apply(induction y) 
    apply(auto)
  done

lemma add_assoc [simp]: "add x (add y z) = add (add x y) z"
  apply(induction x)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" | "double (Suc n) = Suc (Suc (double n))"

value "double 4"

lemma double1 [simp]: "add x x = double x"
  apply(induction x)
   apply(auto)
  done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y#ys) =
  (if x = y then 1 else 0)
  + count x ys"

lemma count1: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" | "snoc (y#ys) x = y # snoc ys x"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" | "reverse (x#xs) = snoc (reverse xs) x"

value "reverse [x,y,z]"

lemma reversiert [simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

lemma reversi: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma sum1: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Leaf = []" | "contents (Node l v r) = contents l @ [v] @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Leaf = 0" | "sum_tree (Node l v r) = sum_tree l + v + sum_tree r"

lemma sum_of_tree: "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf v) = Leaf v" |
"mirror (Node l v r) = Node (mirror r) v (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf v) = [v]" |
"pre_order (Node l v r) = pre_order l @ [v] @ pre_order r"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf v) = [v]" |
"post_order (Node l v r) = post_order r @ [v] @ post_order l"

value "[1,2] @ [1] :: nat list"

lemma split_rev [simp]: "rev (xs @ ys) = rev ys @ rev xs"
  apply(induction xs)
  apply(induction ys)
    apply(auto)
  done

lemma "pre_order (mirror t) = (post_order t)"
  apply(induction t)
   apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # y # xs) = x # a # intersperse a (y # xs)"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
    apply(auto)
  done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 y = y" |
"itadd (Suc x) y = itadd x (Suc y)"

lemma "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node l r) = nodes l + 1 + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma "nodes (explode n t) = 2 ^ n * (nodes t) + 2 ^ n - 1"
  apply(induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) x = n" |
"eval (Add a b) x = eval a x + eval b x" |
"eval (Mult a b) x = eval a x * eval b x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (p#ps) x = p + evalp ps x * x"

fun merge :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"merge [] ys = ys" |
"merge xs [] = xs" |
"merge (x#xs) (y#ys) = (x+y) # merge xs ys"

fun mul :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mul (x#xs) ys = merge (map ((*) x) ys) (mul xs (0#ys))" |
"mul _ ys = map ((*) 0) ys"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const x) = [x]" |
"coeffs (Add x y) = merge (coeffs x) (coeffs y)" |
"coeffs (Mult x y) = mul (coeffs x) (coeffs y)"

lemma evalp_decomp_add [simp]: "evalp (merge e1 e2) x = evalp e1 x + evalp e2 x"
  apply(induction rule: merge.induct)
    apply(auto simp add: algebra_simps)
  done

lemma map_mul [simp]: "evalp (map ((*) a) e) x = a * evalp e x"
  apply(induction e)
   apply(auto simp add: algebra_simps)
  done

lemma mul_comm [simp]: "mul e1 (0 # e2) = 0 # mul e1 e2"
  apply(induction e1 arbitrary: e2)
   apply(auto simp add: algebra_simps)
  done

lemma evalp_decomp_zero [simp]: "evalp (0 # e) x = x * evalp e x"
  apply(induction e)
   apply(auto)
  done

lemma evalp_decomp_mul [simp]: "evalp (mul e1 e2) x = evalp e1 x * evalp e2 x"
  apply(induction e1)
    apply(auto simp add: algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
     apply(auto simp add: algebra_simps)
  done

(* Chapter 3 *)
datatype 'a tree1 = Tip | Node "'a tree1" 'a "'a tree1"

fun set :: "'a tree1 \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l v r) = set l Un {v} Un set r"

fun ord :: "int tree1 \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l v r) = ((\<forall>x\<in>set l. x < v) & (\<forall>x\<in>set r. x > v) & ord l & ord r)"

fun ins :: "int \<Rightarrow> int tree1 \<Rightarrow> int tree1" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l v r) =
(let left = (if x < v then ins x l else l) in
let right = (if x > v then ins x r else r) in
Node left v right)"

lemma first [simp]: "set (ins x t) = {x} Un set t"
  apply(induction t)
  apply(auto)
  done

lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)
  apply(simp)
  apply(auto simp add: algebra_simps)
  done

lemma "\<forall>xs\<in>A. \<exists>ys. xs = ys @ ys \<Longrightarrow> us \<in> A  \<Longrightarrow> \<exists>n. length us = n + n"
  by fastforce

inductive ev :: "nat \<Rightarrow> bool" where
base_ev: "ev 0" |
step_ev: "ev n \<Longrightarrow> ev (n+2)"

lemma "ev 0"
  apply(rule base_ev)
  done

inductive palindrome :: "'a list \<Rightarrow> bool" where
base0: "palindrome []" |
base1: "palindrome [x]" |
step: "palindrome xs \<Longrightarrow> palindrome (x # xs @ [x])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule: palindrome.induct)
    apply(auto)
  done

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans [simp]: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(simp)
  apply(simp)
  apply(rule step)
   apply(simp)
  apply(simp)
  done

lemma star_r [simp]: "r x y \<Longrightarrow> star r x y"
  apply(rule step)
   apply(auto)
  apply(rule refl)
  done

lemma star'_r [simp]: "r x y \<Longrightarrow> star' r x y"
  apply(rule step')
   apply(auto)
  apply(rule refl')
  done

lemma star'_trans [simp]: "star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(auto dest: star'_r)
  apply(rule step')
   apply(auto dest: star'_r)
  done

lemma "star' r x y = star r x y"
  apply(intro iffI)
  apply(induction rule: star'.induct)
    apply(rule refl)
   apply(rule star_trans)
    apply(simp)
   apply(rule star_r)
   apply(simp)

  apply(induction rule: star.induct)
   apply(rule refl')
  apply(rule star'_trans)
  apply(simp)
  apply(rule star'_r)
  apply(simp)
  done

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
zero: "iter r 0 x x" |
add: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

theorem "star r x y \<Longrightarrow> EX n. iter r n x y"
  apply(induction rule: star.induct)
   apply(meson zero)
  apply(meson add)
  done

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
sempty [simp]: "S []" |
sbrace: "S x \<Longrightarrow>  S (a # x @ [b])" |
ssplit: "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

inductive T :: "alpha list \<Rightarrow> bool" where
tempty [simp]: "T []" |
tbrace [simp]: "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ a # y @ [b])"

lemma "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(auto simp add: ssplit sbrace)
  done

(*
UNFINISHED

lemma conc: "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ y)"
  apply(induction rule: T.induct)
   apply(simp)
  apply(simp)
  apply(induction y)
   apply(simp)
  apply(rule tbrace)
  done

lemma "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(rule tempty)
  using T.simps append_self_conv2 tempty apply blast
  apply(rule conc)
  done
*)

thm surj_def
lemma "~surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "ALL y. EX x. y = f x" by (simp add: surj_def)
  from 1 have 2: "EX x. {a. a \<notin> f a} = f x" by blast
  from 2 show "False" by blast
qed

lemma
  fixes A T :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
and x y :: 'a
assumes T: "ALL x y. T x y \<or> T y x"
and A: "ALL x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "ALL x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof cases
  assume "x = y"
  from this T show "T x y" by auto
next
  assume "~ (x = y)"
  from this A assms(4) have "~ A y x" by auto
  from this TA have "~ T y x" by blast
  from this T show "T x y" by blast
qed

fun even :: "nat \<Rightarrow> bool" where
"even x = (\<exists>k. x = 2*k)"

lemma ln_ev: "even n \<longrightarrow> n div 2 = n - (n div 2)"
  by auto

lemma ln_odd: "~ even n \<longrightarrow> n div 2 + 1 = n - (n div 2)"
  by (smt add.commute add_diff_cancel_right' dvd_mult_div_cancel even.elims(3) group_cancel.add1 mult_2 odd_two_times_div_two_succ)

lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume c1: "even (length xs)"
  let ?ys = "take (length xs div 2) xs"
  let ?zs = "drop (length xs div 2) xs"
  from c1 ln_ev have ln: "length ?ys = length xs div 2 \<and> length ?zs = length xs div 2" by fastforce
  from this have "xs = ?ys @ ?zs" by simp
  from this ln have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by simp
  from this show "\<exists> ys zs . xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)" by blast
next
  assume c2: "~ even (length xs)"
  let ?ys = "take (length xs div 2 + 1) xs"
  let ?zs = "drop (length xs div 2 + 1) xs"
  from c2 ln_odd have ln: "length ?ys = length xs div 2 + 1 \<and> length ?zs = length xs div 2" by simp
  from this have "xs = ?ys @ ?zs" by simp
  from this ln have "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by simp
  from this show "\<exists> ys zs . xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)" by blast
qed

(*
inductive ev :: "nat \<Rightarrow> bool" where
base_ev: "ev 0" |
step_ev: "ev n \<Longrightarrow> ev (n+2)"
*)

lemma "~ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  from this have "ev (Suc 0)"
  proof cases
    case step_ev
    thus "ev (Suc 0)" by (simp add: ev.step_ev)
  qed
  from this show False by (metis add_is_1 ev.simps n_not_Suc_n nat.distinct(1) numeral_2_eq_2)
qed

lemma
  assumes a: "ev n"
  shows "ev (n-2)"
proof -
  from a show "ev (n-2)"
  proof cases
    case base_ev
    thus "ev (n-2)" by (simp add: ev.base_ev)
  next
    case (step_ev k)
    thus "ev (n-2)" by (simp)
  qed
qed

lemma "ev n \<Longrightarrow> ev (n-2)"
proof -
  assume "ev n"
  from this show "ev (n-2)"
  proof cases
    case base_ev
    thus "ev (n-2)" by (simp add: ev.base_ev)
  next
    case (step_ev k)
    thus "ev (n-2)" by (simp add: ev.step_ev)
  qed
qed

(*
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
zero: "iter r 0 x x" |
add: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
*)

lemma
  shows "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (zero x)
  then show ?case by (auto simp add: star.refl)
next
  case (add x y n z)
  then show ?case by (auto simp add: star.step)
qed

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = {x} Un (elems xs)"

lemma elem_list: "x: elems xs \<Longrightarrow> EX n. x = hd (drop n xs)"
proof (induction xs)
  case Nil
  then have "x \<notin> elems xs" by simp
  then show "x \<in> elems [] \<Longrightarrow> \<exists>n. x = hd (drop n [])" by auto
next
  case (Cons a xs)
  then show "\<exists>n. x = hd (drop n (a # xs))"
  proof (cases "x = a")
    case True
    then show "x = a \<Longrightarrow> \<exists>n. x = hd (drop n (a # xs))"
      by (metis hd_drop_conv_nth length_Cons nth_Cons_0 zero_less_Suc) 
  next
    case False
    assume "x: elems (a # xs)"
    from this False have 0: "x: elems xs" by simp
    assume "x \<in> elems xs \<Longrightarrow> \<exists>n. x = hd (drop n xs)"
    from this 0 show ?thesis
    by (metis Cons_nth_drop_Suc Groups.add_ac(2) One_nat_def drop0 drop_drop elems.elims length_Cons list.discI list.sel(3) nth_Cons_0 plus_1_eq_Suc zero_less_Suc)
  qed
qed

type_synonym sprache = nat

fun nuetze :: "sprache \<Rightarrow> sprache \<Rightarrow> bool" where
"nuetze x y = (x > y)"

lemma
  fixes "ocaml"
  shows "\<forall>sprache. sprache \<noteq> ocaml \<longrightarrow> nuetze sprache ocaml \<Longrightarrow> False"
  by try

lemma
  fixes x :: 'a
  and xs :: "'a list"
  assumes "x: elems xs"
  shows "EX ys zs. xs = ys @ x # zs" (* \<and> x \<notin> elems ys"*)
proof -
  from assms have "EX n. x = hd (drop n xs)" by (auto simp add: elem_list)
  then obtain n where "x = hd (drop n xs)" by auto
  obtain ys where "ys = take (n) xs" by auto
  obtain zs where "zs = drop (n+1) xs" by auto
  have "xs = ys @ x # zs" by try




















































end