import Mathlib.Tactic

/-!
# Tactic notes


这些例子偏向教学用途：每个 tactic 只保留能说明用法的代表性片段。
-/

section Basic

/-!
## 1. `exact` 和 `rfl`

* `exact h`：用一个已经具有目标类型的项/定理完成目标。
* `rfl`：证明两边按定义相同的等式。
-/

example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (x y : ℝ) : x + 37 * y = x + 37 * y := by
  rfl

/-!
## 2. `apply`

`apply` 用一个定理反推当前目标需要哪些前提。没有填上的参数会变成新的目标。
-/

example {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans h1 h2

example {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans (b := b)
  · exact h1
  · exact h2

example {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans ?_ h2
  exact h1

/-!
## 3. `rw`、`nth_rw` 和 `have`

* `rw [h]`：用等式或 iff 改写目标。
* `rw [h] at h₂`：在某个假设中改写。
* `rw [← h]`：反向改写。
* `nth_rw 2 [h]`：只改写第 2 个匹配项。
* `have`：先证明一个中间结论。
-/

example {a b c d : ℝ} (h1 : a = c) (h2 : b = d) : a * b = c * d := by
  rw [h1]
  rw [h2]

example (a : ℝ) : a * 0 + a * 0 = a * 0 := by
  rw [← mul_add, add_zero]

example (a b c : ℝ) : a * (b * c) = a * (c * b) := by
  rw [mul_comm b c]

example (a b c : ℝ) (h : a + b = c) :
    (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

example (a : ℝ) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  exact add_left_cancel h

/-!
## 4. `suffices`、`assumption` 和 `refine`

* `suffices h : P`：把当前目标转化为“只要证明 `P` 就够了”。
* `assumption`：在上下文中搜索能直接完成目标的假设。
* `refine`：像 `apply`，但允许用 `?_` 留洞。
-/

example (P Q R : Prop) (h1 : P → R) (h2 : Q) (h3 : Q → P) : R := by
  suffices hp : P by
    exact h1 hp
  exact h3 h2

example (a b : ℝ) (h : a = b) : a = b := by
  assumption

example (P Q R : Prop) (hP : P) (hQ : Q) (hPR : P → R) : Q ∧ R := by
  refine ⟨hQ, ?_⟩
  exact hPR hP

end Basic

section Logic

/-!
## 5. 逻辑目标：`constructor`、`left`、`right`、`intro`、`use`

* 目标是 `P ∧ Q` 或 `P ↔ Q` 时，常用 `constructor`。
* 目标是 `P ∨ Q` 时，用 `left` 或 `right` 选择一边。
* 目标是全称命题或蕴含时，用 `intro` 引入变量/假设。
* 目标是存在命题时，用 `use` 给出见证。
-/

variable {x y : ℝ}

example (h0 : x ≤ y) (h1 : x ≠ y) : x ≤ y ∧ x ≠ y := by
  constructor
  · exact h0
  · exact h1

example (h : y > 0 ∧ y < 8) : y > 0 ∨ y < -1 := by
  left
  exact h.left

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := by
  intro a b hab
  exact h hab

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 3
  constructor <;> norm_num

/-!
## 6. 逻辑假设：`.left` / `.right`、`rcases`、`rintro`、`obtain`

当假设中有合取、析取、存在命题时，`rcases` 很方便。
`rintro` 则是 `intro` 后立刻做模式匹配的简写。
`obtain` 相当于先得到一个中间结论，再立刻用 `rcases` 拆开。
-/

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  exact lt_of_le_of_ne h.left h.right

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  rcases h with ⟨h_le, h_ne⟩
  exact lt_of_le_of_ne h_le h_ne

example {x : ℝ} (h : x = 3 ∨ x = 5) : x = 3 ∨ x = 5 := by
  rcases h with h | h
  · left
    exact h
  · right
    exact h

example {α : Type} {s t u : Set α} (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨mem_s, mem_u⟩
  exact ⟨h mem_s, mem_u⟩

example {α : Type} {p : α → Prop} (h : ∃ x, p x) : ∃ x, p x := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx⟩

/-!
## 7. `cases`

`cases` 对归纳类型或析取命题分情况讨论。和 `induction` 不同，`cases` 不会给归纳假设。
-/

example {P Q R : Prop} (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl hP => exact hp hP
  | inr hQ => exact hq hQ

example (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 := by
  cases n with
  | zero =>
      left
      rfl
  | succ k =>
      right
      exact ⟨k, rfl⟩

/-!
## 8. 否定和矛盾：`push Not`、`exfalso`、`contradiction`、`by_contra`、`contrapose`

* `push Not` 把否定往命题内部推进。旧讲义中的 `push_neg` 现在推荐写成 `push Not`。
* `exfalso` 把目标改成 `False`。
* `contradiction` 尝试从上下文里的矛盾结束证明。
* `by_contra h` 用反证法，把目标的否定加入上下文。
* `contrapose! h` 把一个假设或目标改成逆否命题，并顺手推进否定。
-/

example {x : ℝ} (h : x < 0) : ¬ 0 ≤ x := by
  push Not
  exact h

example {x : ℝ} (h : ¬ 0 ≤ x) : x < 0 := by
  push Not at h
  exact h

example {P Q : Prop} (hP : P) (hnP : ¬ P) : Q := by
  exfalso
  exact hnP hP

example {P : Prop} (hP : P) (hnP : ¬ P) : False := by
  contradiction

example {P : Prop} (h : ¬¬ P) : P := by
  by_contra hnP
  exact h hnP

example {x y : ℝ} (h : x ≤ y) : ¬ y < x := by
  contrapose! h
  exact h

/-!
## 9. `simp`、`simp_all` 和 `tauto`

* `simp` 用 simp 定理化简目标和假设。
* `simp only [...]` 只使用指定定理。
* `simp_all` 会同时化简目标和所有假设，并使用假设做替换。
* `tauto` 适合纯逻辑命题。
-/

example {α : Type} {s t : Set α} {x : α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  simp only [Set.mem_union]

example {α : Type} {x : α} {s t : Set α} (h1 : x ∈ s) (h2 : x ∈ t) :
    x ∈ s ∩ t := by
  simp only [Set.mem_inter_iff]
  exact ⟨h1, h2⟩

example {x y : Nat} (h : x = y) : x + 1 = y + 1 := by
  simp_all

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  tauto

end Logic

section RewritingAndDefinitions

/-!
## 10. 定义和目标形状：`unfold`、`dsimp`、`change`、`show`

* `unfold f` 展开定义 `f`。
* `dsimp` 做定义化简。
* `change T` 把目标改写成定义相同的新形式。
* `show T` 明确告诉 Lean 当前要证明的目标形状。
-/

def double (n : Nat) : Nat := n + n

example (n : Nat) : double n = n + n := by
  unfold double
  rfl

example (n : Nat) : (fun x : Nat => x + 0) n = n := by
  dsimp

example (a b : ℝ) : a - b = a + (-b) := by
  change a + (-b) = a + (-b)
  rfl

example : (2 : Nat) + 2 = 4 := by
  show 4 = 4
  rfl

/-!
## 11. `repeat`

`repeat tac` 会重复执行某个 tactic，直到它不能继续使用为止。
-/

example (a b c : ℝ) : ((a * b) * c) = a * (b * c) := by
  repeat rw [mul_assoc]

end RewritingAndDefinitions

section FunctionalExtensionality

/-!
## 12. `funext`

`funext` 使用函数外延性，把函数相等转成任意输入处取值相等。
-/

example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-!
## 13. `congr`

`congr` 根据同余性把复杂等式拆成子目标。它常和 `ext`、`simp`、`ring` 搭配。
-/

example (a b c : ℝ) (h : a = b) : a + c = b + c := by
  congr

example (f : ℝ → ℝ) (a b : ℝ) (h : a = b) : f (a + 1) = f (b + 1) := by
  congr 1
  rw [h]

end FunctionalExtensionality

section CalcAndExt

/-!
## 14. `calc`

`calc` 把等式或不等式链分成若干可读步骤。
-/

example (a b c : ℝ) : a + b + c = c + b + a := by
  calc
    a + b + c = (a + b) + c := by rfl
    _ = c + (a + b) := by rw [add_comm]
    _ = c + (b + a) := by rw [add_comm a b]
    _ = c + b + a := by rw [add_assoc]

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  calc
    2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]

/-!
## 15. `ext`

`ext` 使用外延性原则。集合相等通常会转成任意元素的双向归属。
-/

example {α : Type} {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

example {α : Type} {s t : Set α} : s ∩ t = t ∩ s := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

end CalcAndExt

section Automation

/-!
## 16. 数值和不等式自动化

* `norm_num`：处理具体数值计算。
* `linarith`：处理线性等式/不等式。
* `nlinarith`：处理一部分非线性算术。
* `omega`：处理自然数/整数线性算术、取模等 Presburger 算术。
* `positivity`：证明表达式正或非负。
* `decide`：处理可判定命题，尤其是具体的有限/布尔/数值判断。
-/

example : (1 : ℝ) + 1 = 2 := by
  norm_num

example : ¬ (5 : ℤ) ∣ 12 := by
  norm_num

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) :
    a + a < d + b := by
  linarith

example {x : ℝ} (h : x ≤ -3) : x ^ 2 ≥ 9 := by
  nlinarith

example (x : ℕ) : x ≥ 2 → x / 2 ≥ 1 := by
  omega

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by
  positivity

example : (3 : Nat) < 5 := by
  decide

/-!
## 17. 代数自动化

* `ring`：交换环中的多项式恒等式。
* `ring_nf`：先把代数表达式正规化。
* `noncomm_ring`：非交换环中的多项式恒等式。
* `field_simp`：清理分母，常和 `ring` 搭配。
-/

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring

example (x y : ℝ) (f : ℝ → ℝ) : f (x + y) + f (y + x) = 2 * f (x + y) := by
  ring_nf

example {R : Type} [Ring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  noncomm_ring

example (x : ℝ) (h : x > 0) : 1 / x + 1 = (x + 1) / x := by
  field_simp [ne_of_gt h]
  ring

/-!
## 18. coercion 相关：`norm_cast` 和 `push_cast`

* `norm_cast at h`：把假设中的强制类型转换规范化。
* `push_cast`：把 coercion 推进到表达式内部。
-/

example (a b : ℤ) (h : (a : ℚ) + b < 10) : a + b < 10 := by
  norm_cast at h

example (a b : Nat)
    (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  push_cast
  push_cast [Int.add_zero] at h2
  exact h2

/-!
## 19. `aesop`

`aesop` 是通用搜索型自动化 tactic，适合一些由构造子、简单逻辑和已有假设组成的目标。
-/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  aesop

example {α : Type} {s t : Set α} {x : α} (hs : x ∈ s) : x ∈ s ∪ t := by
  aesop

end Automation

section MoreCommonTactics

/-!
## 20. 上下文管理：`specialize`、`clear`、`replace`、`subst`

* `specialize h a b`：把全称命题/函数型假设 `h` 应用到参数上。
* `clear h`：删除当前证明中不再需要的假设。
* `replace h : P := ...`：用一个新结论替换旧的同名假设。
* `subst x`：用等式假设把变量 `x` 替换掉。
-/

example {P Q R : Prop} (h : P → Q → R) (hp : P) (hq : Q) : R := by
  specialize h hp hq
  exact h

example {P : Prop} (hp : P) : P := by
  have h : True := by trivial
  clear h
  exact hp

example {a b c : ℝ} (h : a = b) (hc : b = c) : a = c := by
  replace h : a = c := by
    rw [h, hc]
  exact h

example {α : Type} {a b : α} (h : a = b) (p : α → Prop) (ha : p a) : p b := by
  subst b
  exact ha

/-!
## 21. 变量引入和回收：`intros`、`revert`、`generalize`

* `intros` 一次引入多个变量/假设。
* `revert x` 把上下文中的变量放回目标里，常用于重新组织归纳目标。
* `generalize h : t = x` 把复杂表达式抽象成新变量，并留下定义等式。
-/

example (P Q : Prop) : P → Q → P ∧ Q := by
  intros hp hq
  exact ⟨hp, hq⟩

example (P Q : Prop) (hp : P) : Q → P := by
  intro hq
  revert hq
  intro _hq
  exact hp

example (n : Nat) : n + 1 = Nat.succ n := by
  generalize h : n + 1 = m
  rw [Nat.add_one] at h
  exact h.symm

/-!
## 22. 构造子信息：`injection`、`cases` + `rename_i`

* `injection h` 从构造子相等推出参数相等。
* `rename_i` 给 `cases`/`induction` 自动生成的变量命名。
-/

example {a b : Nat} (h : Nat.succ a = Nat.succ b) : a = b := by
  injection h

example (n : Nat) : n = 0 ∨ ∃ k : Nat, n = Nat.succ k := by
  cases n with
  | zero =>
      left
      rfl
  | succ =>
      rename_i k
      right
      exact ⟨k, rfl⟩

/-!
## 23. `trivial`、`native_decide`

* `trivial` 证明显然为真的命题，例如 `True`。
* `native_decide` 用本地编译求值证明可判定命题，适合较大的具体计算。
-/

example : True := by
  trivial

example : (1000 : Nat) < 1001 := by
  native_decide

/-!
## 24. 类型和目标转换：`convert`

`convert h` 尝试用一个“几乎同型”的证明完成目标，并把差异留下来作为子目标。
-/

example (a b : ℝ) (h : a + b = b + a) : a + b = b + a + 0 := by
  convert h using 1
  rw [add_zero]

/-!
## 25. 更细粒度的改写：`simp_rw` 和 `conv`

* `simp_rw [h]` 类似 `rw`，但会在更深层、重复地改写。
* `conv` 可以进入表达式的局部位置做改写。
-/

example (f : Nat → Nat) (h : ∀ n, f n = n) : f (f 3) = 3 := by
  simp_rw [h]

example (a b c : ℝ) : (a + b) + c = (b + a) + c := by
  conv_lhs =>
    rw [add_comm a b]

/-!
## 26. 有限情况自动拆分：`fin_cases` 和 `interval_cases`

* `fin_cases i` 枚举 `Fin n` 的所有元素。
* `interval_cases n` 利用上下界枚举自然数/整数的有限范围。
-/

example (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · left
    rfl
  · right
    rfl

example (n : Nat) (h1 : 2 ≤ n) (h2 : n ≤ 4) : n = 2 ∨ n = 3 ∨ n = 4 := by
  interval_cases n
  · left
    rfl
  · right
    left
    rfl
  · right
    right
    rfl

end MoreCommonTactics

section Induction

/-!
## 27. `induction`

`induction n with` 对归纳类型做数学归纳法。对自然数会产生 `zero` 和 `succ` 两个分支。
-/

def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : Nat) : fac n > 0 := by
  induction n with
  | zero =>
      rw [fac]
      decide
  | succ n ih =>
      rw [fac]
      apply Nat.mul_pos
      · exact Nat.succ_pos n
      · exact ih

example (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, ih]

end Induction

section Combinators

/-!
## 28. tactic 组合：`;`、`<;>`、`all_goals`、`any_goals`、`try`、`first` 和 `split_ands`

* `tac1; tac2` 会在 `tac1` 产生的第一个目标后运行 `tac2`。
* `tac1 <;> tac2` 会在 `tac1` 产生的所有目标上运行 `tac2`。
* `all_goals tac` 在所有当前目标上运行同一个 tactic。
* `any_goals tac` 在所有能成功的目标上运行 tactic。
* `try tac` 尝试运行 tactic，失败也不报错。
* `first | tac₁ | tac₂` 从上到下尝试 tactic，取第一个成功者。
* `split_ands` 可以连续拆开多个合取目标。
-/

example : (1 : ℝ) < 2 ∧ (2 : ℝ) < 3 := by
  constructor <;> norm_num

example : (1 : Nat) = 1 ∧ (2 : Nat) = 2 := by
  constructor
  all_goals rfl

example : (1 : Nat) = 1 ∧ True := by
  constructor
  any_goals rfl
  trivial

example : True := by
  try rfl
  trivial

example : (2 : Nat) = 2 := by
  first
  | contradiction
  | rfl

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  set x := (b - a + c) / 2 with hx_def
  set y := (a - b + c) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  use x, y, z
  split_ands <;> linarith

end Combinators

section Diagnostics

/-!
## 29. 查询和诊断：`#check`、`#print`、`guard_target`、`guard_hyp`、`trace_state`

`#check` 和 `#print` 是命令，不是 tactic；它们常用于查询定理类型或定义内容。
`guard_target`、`guard_hyp`、`trace_state` 用于调试 tactic 状态。
-/

#check Nat.succ
#check add_comm
#print Nat.succ

example (a b : ℝ) (h : a = b) : a = b := by
  guard_target =ₛ a = b
  guard_hyp h : a = b
  exact h

example (P : Prop) (h : P) : P := by
  trace_state
  exact h

end Diagnostics

section TypeclassTactics

/-!
## 30. 类型类与实例：`infer_instance`、`exact_mod_cast`

* `infer_instance` 构造当前目标所需的类型类实例。
* `exact_mod_cast h` 在自然数、整数、有理数、实数等类型之间处理 coercion 后使用 `h`。

注：旧资料中有时会提到 `apply_instance`；在当前 Lean/mathlib 环境下直接使用
`infer_instance` 更稳妥。
-/

example : DecidableEq Nat := by
  infer_instance

example : LinearOrder Nat := by
  infer_instance

example (a b : ℕ) (h : a = b) : (a : ℤ) = b := by
  exact_mod_cast h

example (a b : ℕ) (h : a ≤ b) : (a : ℤ) ≤ b := by
  exact_mod_cast h

end TypeclassTactics

section SpecializedAutomation

/-!
## 31. 专门自动化：`abel`、`group`、`linear_combination`

* `abel` 处理交换加法群中的恒等式。
* `group` 处理群表达式。
* `linear_combination` 从线性组合假设推出等式。

注：旧版 mathlib 中曾有 `polyrith`，但当前版本已经下线；多项式等式通常用
`ring`、`nlinarith`、`linear_combination` 等组合替代。
-/

example {G : Type} [AddCommGroup G] (a b : G) : a + b - a = b := by
  abel

example {G : Type} [Group G] (a b : G) : a * b * b⁻¹ = a := by
  group

example (x y : ℚ) (h1 : x + y = 10) (h2 : x - y = 4) : 2 * x = 14 := by
  linear_combination h1 + h2

example (x y : ℚ) (h1 : x + y = 10) (h2 : x - y = 4) : x = 7 := by
  linear_combination (h1 + h2) / 2

example (x : ℚ) (h : x ^ 2 = 4) : (x ^ 2 - 4) ^ 2 = 0 := by
  rw [h]
  ring

end SpecializedAutomation

section ProofStructure

/-!
## 32. 证明脚本结构：`case`、`next`、`focus`、`swap`、`rotate_left`、`rotate_right`

这些 tactic/语法帮助管理多个目标。

* `case` 按名字进入指定分支。
* `next` 顺序处理匿名分支。
* `focus` 暂时聚焦当前目标。
* `swap` 交换前两个目标。
* `rotate_left` / `rotate_right` 轮转目标顺序。
-/

example (n : Nat) : n + 0 = n := by
  induction n
  case zero =>
    rfl
  case succ n ih =>
    rw [Nat.succ_add, ih]

example : True ∧ True := by
  constructor
  next =>
    trivial
  next =>
    trivial

example : True ∧ True := by
  constructor
  focus
    trivial
  trivial

example : True ∧ (1 : Nat) = 1 := by
  constructor
  swap
  · rfl
  · trivial

example : True ∧ (1 : Nat) = 1 ∧ (2 : Nat) = 2 := by
  constructor
  rotate_left
  · constructor
    · rfl
    · rfl
  · trivial

example : (1 : Nat) = 1 ∧ True := by
  constructor
  rotate_right
  · trivial
  · rfl

end ProofStructure

section ConvMore

/-!
## 33. 更完整的 `conv`：`lhs`、`rhs`、`enter`

`conv` 可以进入目标表达式内部进行局部改写。

* `lhs` 进入等式左边。
* `rhs` 进入等式右边。
* `enter [i]` 进入函数应用的第 `i` 个参数。
-/

example (a b c : ℝ) : (a + b) + c = (b + a) + c := by
  conv =>
    lhs
    rw [add_comm a b]

example (a b c : ℝ) : a + (b + c) = a + (c + b) := by
  conv =>
    rhs
    enter [2]
    rw [add_comm c b]

example (f : ℝ → ℝ) (a b : ℝ) : f (a + b) = f (b + a) := by
  conv =>
    rhs
    enter [1]
    rw [add_comm b a]

end ConvMore

/-!
建议掌握顺序：先熟练 `intro`/`apply`/`exact`/`rw`/`simp`/`rcases`/`constructor`，
再逐步使用自动化、上下文管理和目标管理 tactic。专门自动化 tactic 很强，但最好在理解
目标结构之后再使用。
-/
