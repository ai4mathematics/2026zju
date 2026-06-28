# D2 | 7月14日（周二）| Inductive Type 与 Class

主题：`inductive`、模式匹配、递归定义、归纳证明、`structure`、常用归纳类型 API、`class` 与 `instance` 机制。当前版本面向数学背景学生，例子尽量围绕自然数递归、数学归纳法、向量结构、代数 type class 与 mathlib 展开。

总时长：3 小时，其中中间休息 20 分钟，实际讲授与练习约 160 分钟。

## 课程目标

本节课结束后，希望学生能够：

1. 会读写简单的 `inductive`、`structure`、`class`。
2. 理解构造子、模式匹配、递归定义和归纳证明之间的关系。
3. 能使用常见归纳类型 `Option`、`List`、`Fin`、`Multiset` 的基本 API。
4. 理解类型类机制如何支持数学中的通用记号与结构，例如 `Add`、`Mul`、`Ring`、`Field`。
5. 能看懂并修改配套 Lean 文件中的小型定义和证明。

## 四部分结构

| Part | 标题 | 内容 |
| --- | --- | --- |
| Part I | Inductive | 归纳类型、构造子、`Weekday`、`MyNat`、递归数据形状 |
| Part II | Recursion and Induction | 模式匹配、自然数递归定义、`add/mul/pow`、归纳证明 |
| Part III | Structures and APIs | `structure`、`Vector2`、带性质的结构、`Option/List/Fin/Multiset` |
| Part IV | Type Classes | `class`、`instance`、`Add/Mul/Ring/Field`、mathlib 代数结构 |

## 总体时间安排

| 时间 | 内容 |
| --- | --- |
| 0-35 min | Part I: Inductive |
| 35-80 min | Part II: Recursion and Induction |
| 80-100 min | 休息 |
| 100-145 min | Part III: Structures and APIs |
| 145-180 min | Part IV: Type Classes 与综合例子 |

## Part I: Inductive，约 35 分钟

核心问题：Lean 中的数据类型如何由构造子生成？构造子的形状如何预示后续的程序和证明？

建议内容：

1. 从常见类型切入：
   - `Bool`
   - `Nat`
   - `Option`
   - `List`

2. 建立主线：
   - 如果知道一个对象如何被构造，就知道如何对它分类讨论。
   - 如果构造方式是递归的，就自然产生递归定义和归纳证明。

3. 保留简单枚举类型 `Weekday`：

   ```lean
   inductive Weekday where
     | mon | tue | wed | thu | fri | sat | sun
     deriving Repr, BEq, DecidableEq
   ```

   教学重点：
   - closed world：所有元素都来自这些构造子。
   - 构造子是生成元素的方式。
   - `deriving` 可以生成打印、布尔相等、可判定相等等实例。

4. 用 `MyNat` 讲构造子作为函数：

   ```lean
   inductive MyNat where
     | zero : MyNat
     | succ : MyNat -> MyNat
   ```

   教学重点：
   - `zero` 是一个值。
   - `succ` 是一个函数。
   - `succ` 的参数是更小的自然数。

5. 类型参数与构造子参数：

   ```lean
   inductive MyOption (alpha : Type) where
     | none : MyOption alpha
     | some : alpha -> MyOption alpha
   ```

   教学重点：
   - `alpha` 是整个类型族的参数。
   - `some` 的参数是某个具体值中存储的数据。

6. 递归归纳类型：
   - `MyNat`
   - `MyList`
   - `Tree`

7. 用 `MyNat.add` 预告递归定义：

   ```lean
   def MyNat.add : MyNat -> MyNat -> MyNat
     | m, zero => m
     | m, succ n => succ (MyNat.add m n)
   ```

Beamer 重点：

- 四个阅读问题：
  1. 新类型是什么？
  2. 构造子是什么？
  3. 哪些构造子携带数据？
  4. 哪些构造子递归？
- slogan：constructor shape predicts program shape and proof shape.

Lean 文件：

```text
code/D2_Inductive.lean
```

## Part II: Recursion and Induction，约 45 分钟

核心问题：递归定义和归纳证明为什么共享同一种结构？

### 2.1 模式匹配

建议内容：

1. 对 `Weekday` 做模式匹配：

   ```lean
   def isWeekend : Weekday -> Bool
   ```

2. 对 `Option` 做模式匹配：
   - `none`
   - `some a`

3. 对 `List` 做模式匹配：
   - `[]`
   - `x :: xs`

教学重点：

- 模式匹配就是按构造子分支。
- 构造子携带的数据会在对应分支中变成可用变量。

### 2.2 自然数上的递归定义

建议内容：

用学生熟悉的数学递归定义作为主线：

```lean
def add (m : Nat) : Nat -> Nat
  | 0 => m
  | n + 1 => add m n + 1

def mul (m : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => mul m n + m

def pow (m : Nat) : Nat -> Nat
  | 0 => 1
  | n + 1 => pow m n * m
```

教学重点：

- 递归发生在第二个变量上。
- 每个定义都对应数学中的递推方程。
- Lean 的结构递归检查保证定义终止。

### 2.3 List 上的递归

保留 `List` 例子作为标准库容器中的递归模式：

- `myLength`
- `myMap`
- `myAppend`
- `sumList`

### 2.4 归纳证明

建议内容：

1. `cases`：
   - `Bool`
   - `Option`

2. 自然数归纳证明：

   ```lean
   theorem zero_add (n : Nat) : add 0 n = n := by
     induction n with
     | zero => rfl
     | succ n ih =>
         calc
           add 0 (n + 1) = add 0 n + 1 := rfl
           _ = n + 1 := by rw [ih]
   ```

3. 可选展示：
   - `add_assoc`
   - list 上的 `append_nil_right`
   - tree 上的 `mirror_mirror`

教学重点：

- base case 对应 `0` 或 `[]`。
- step case 对应 `succ n` 或 `x :: xs`。
- induction hypothesis 来自递归子对象。

Beamer 重点：

- 表格展示：

  | Data | Program | Proof |
  | --- | --- | --- |
  | base constructor | base branch | base case |
  | recursive constructor | recursive call | induction hypothesis |

Lean 文件：

```text
code/D2_PatternMatching.lean
code/D2_InductionProofs.lean
```

## 休息，20 分钟

休息页保留一个问题：

如果一个树节点包含两个子树，那么递归程序和归纳证明应该分别长什么样？

这个问题用于连接 tree recursion 和后续更复杂的结构化对象。

## Part III: Structures and APIs，约 45 分钟

核心问题：Lean 如何打包数学对象？常见归纳类型在数学建模中分别适合什么场景？

### 3.1 `structure`

建议内容：

用二维整数向量作为主要例子：

```lean
structure Vector2 where
  x : Int
  y : Int
  deriving Repr, BEq, DecidableEq
```

定义常见操作：

```lean
def Vector2.add (u v : Vector2) : Vector2 :=
  { x := u.x + v.x, y := u.y + v.y }

def Vector2.dot (u v : Vector2) : Int :=
  u.x * v.x + u.y * v.y
```

教学重点：

- `structure` 打包命名字段。
- `u.x`、`u.y` 是字段访问。
- record syntax 对应坐标定义。

### 3.2 打包数据和性质

用带性质的结构展示 Lean 中数学对象的典型形态：

```lean
structure PointOnDiagonal where
  x : Int
  y : Int
  onDiagonal : x = y
```

教学重点：

- structure 不只打包数据，也可以打包证明。
- 这是数学对象 formalization 的常见模式。
- 后续的群、环、拓扑空间等都可以理解为“数据 + 公理”的结构。

### 3.3 常用归纳类型 API

不要做成 API 列表，而是讲每种类型适合什么建模场景：

| 类型 | 含义 | 用途 |
| --- | --- | --- |
| `Option alpha` | 可能有值，也可能没有 | 部分函数、查找失败 |
| `List alpha` | 有序有限数据 | 递归、遍历、序列 |
| `Fin n` | 小于 `n` 的自然数 | 安全索引、矩阵指标、有限选择 |
| `Multiset alpha` | 无序但有重数的数据 | 组合数学、重集 |

`Multiset` 依赖 mathlib，如果课程环境未配置 mathlib，可在 slides 中讲概念，在 Lean 代码里先保留注释。

Lean 文件：

```text
code/D2_Structure.lean
code/D2_CommonTypes.lean
```

## Part IV: Type Classes，约 35 分钟

核心问题：Lean 如何自动寻找一个类型上的数学结构？同一个数学记号如何用于不同类型？

### 4.1 先用小型自定义 class 解释机制

使用一个偏数学但简单的例子：

```lean
class HasNorm (alpha : Type) where
  norm : alpha -> Nat

def doubleNorm [HasNorm alpha] (x : alpha) : Nat :=
  2 * HasNorm.norm x
```

教学重点：

- `class` 类似可以被自动搜索的 `structure`。
- `[HasNorm alpha]` 表示让 Lean 自动寻找实例。
- `instance` 注册具体类型上的结构。

### 4.2 数学记号来自 type class

核心例子：

```lean
#synth Add Nat
#synth Add Int
#synth Mul Nat
#synth Mul Int
```

以及泛型函数：

```lean
def addThree {alpha : Type} [Add alpha] (a b c : alpha) : alpha :=
  a + b + c
```

教学重点：

- `+` 的含义由 `Add alpha` 实例决定。
- `*` 的含义由 `Mul alpha` 实例决定。
- 同一个 notation 可以服务于多个数学类型。

### 4.3 Mathlib 中的代数结构

如果课程环境包含 mathlib，展示：

```lean
import Mathlib

#synth Add ℕ
#synth Add ℤ
#synth Add ℚ
#synth Add ℂ

#synth Ring ℤ
#synth Field ℚ
#synth Field ℂ
```

教学重点：

- mathlib 提供丰富的代数层级。
- `Add` 只给出运算，不给出结合律、交换律等定律。
- 要使用代数定律，需要更强的 class：
  - `AddCommMonoid`
  - `Ring`
  - `Field`

典型泛型定理：

```lean
example {alpha : Type} [AddCommMonoid alpha] (a b : alpha) :
    a + b = b + a := by
  exact add_comm a b

example {alpha : Type} [Ring alpha] (a b c : alpha) :
    a * (b + c) = a * b + a * c := by
  exact left_distrib a b c
```

### 4.4 `deriving`

`deriving` 不作为数学主线，但仍然保留：

```lean
inductive Color where
  | red | green | blue
  deriving Repr, BEq, DecidableEq
```

教学重点：

- 对自定义类型生成打印、布尔相等、可判定相等。
- 方便课堂演示和练习。

Lean 文件：

```text
code/D2_Typeclass.lean
code/D2_Typeclass_Mathlib.lean
```

注意：

- `D2_Typeclass.lean` 不依赖 mathlib，可以在当前 Lean 环境中运行。
- `D2_Typeclass_Mathlib.lean` 需要 Lake/mathlib 项目。

## 综合例子与总结，约 10 分钟

当前综合例子仍使用表达式树：

```lean
inductive Expr where
  | const : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | var : String -> Expr
  deriving Repr, BEq, DecidableEq
```

围绕它回顾：

1. `inductive` 定义语法树。
2. 模式匹配定义求值或变量收集函数。
3. `Option` 表示变量查找失败。
4. `List` 收集变量名。
5. `structure` 打包环境。
6. `deriving` 生成基础实例。
7. `induction` 证明递归函数性质。

后续如果希望进一步数学化，可以把 `Expr` 改成一元多项式表达式：

```lean
inductive PolyExpr where
  | const : Nat -> PolyExpr
  | var : PolyExpr
  | add : PolyExpr -> PolyExpr -> PolyExpr
  | mul : PolyExpr -> PolyExpr -> PolyExpr
```

## 配套文件

Beamer slides：

```text
slides/D2_inductiveType.tex
```

Lean demo files：

```text
code/D2_Inductive.lean
code/D2_PatternMatching.lean
code/D2_InductionProofs.lean
code/D2_Structure.lean
code/D2_CommonTypes.lean
code/D2_Typeclass.lean
code/D2_Typeclass_Mathlib.lean
code/D2_IntegratedExample.lean
code/D2_Exercises.lean
code/D2_Exercises_Solutions.lean
```

Instructor-facing demo plan：

```text
slides/D2_inductive_class_demo_plan.md
```

## 设计原则

这节课的主线是：

```text
inductive -> pattern matching / recursion -> induction -> structure -> class
```

面向数学背景学生时，建议突出：

1. 自然数递归和数学归纳法。
2. 结构体作为数学对象的打包方式。
3. `Fin`、`Multiset` 在有限数学对象中的建模意义。
4. type class 对数学记号和代数层级的支持。
5. mathlib 中同一个定理如何通过 `[Ring R]`、`[Field K]` 等参数适用于许多数学对象。
