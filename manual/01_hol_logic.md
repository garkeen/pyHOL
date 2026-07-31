# HOL 逻辑基础

> 本章是高阶逻辑（Higher-Order Logic, HOL）的纯理论介绍，不涉及任何 holpy 代码。后续章节在此基础上引入 kernel 实现。

## 1. 类型

在高阶逻辑中，每个项都有唯一的类型。类型由三种构造器组成。

### 1.1 基本类型

- **布尔** `bool`：无参数的类型常量。
- **函数** `A ⇒ B`（也写作 `A => B`）：从类型 `A` 到类型 `B` 的函数。`⇒` 向右结合，故 `A ⇒ B ⇒ C` 等价于 `A ⇒ (B ⇒ C)`。
- **自然数** `nat`、**整数** `int`、**实数** `real`：后续通过归纳类型或公理化引入。

### 1.2 类型构造器

类型常量可以带参数，称为**类型构造器**。例如：

- `nat list`：元素为自然数的列表（`list` 接受一个参数）。
- `A * B`：类型 `A` 与 `B` 的乘积（`prod` 接受两个参数）。

### 1.3 Currying

多参数函数通过 **currying** 表示。接受两个自然数并返回一个自然数的函数类型为 `nat ⇒ nat ⇒ nat`（即 `nat ⇒ (nat ⇒ nat)`）。这与 `(nat ⇒ nat) ⇒ nat`（接受一个函数作为参数）完全不同。

一般地，类型 `A₁ ⇒ … ⇒ Aₙ ⇒ C` 表示接受 `A₁, …, Aₙ` 作为参数、返回 `C` 的函数。

### 1.4 类型变量

**类型变量** `'a` 表示一个任意但固定的类型。它出现在多态定理中，例如相等的类型是 `'a ⇒ 'a ⇒ bool`--对任意类型 `a` 都成立。

**Schematic 类型变量** `?'a` 表示一个可以被任意类型替换的变量。它通常出现在定理陈述中，表示"对任意类型成立"。两者的区别在于：schematic 变量可以被实例化（替换为具体类型），而普通类型变量是固定的。

### 1.5 替换与匹配

含 schematic 类型变量的类型可视为产生具体类型的**模式**。给每个 schematic 变量赋一个具体类型，就得到一个具体类型--这叫**替换**（substitution）。

**匹配**（matching）是替换的对偶：给定模式 `p`（含类型变量）和类型 `t`，判断 `p` 能否实例化为 `t`，若能则返回类型变量的赋值。同一个类型变量在模式中多次出现时，匹配要求所有出现都赋为同一类型。

## 2. 项

项（term）是高阶逻辑语言的基本构造块。有六种项构造器。

### 2.1 变量与常量

- **变量** `Var(name, T)`：给定名字和类型的变量，表示一个任意但固定的值。
- **常量** `Const(name, T)`：表示固定数学概念，如 `true`、`false`、`zero`、`plus` 等。常量由理论定义。
- **Schematic 变量** `SVar(name, T)`：可被任意项替换的变量，用于匹配与替换。打印时前面带 `?`。

### 2.2 函数应用（Combination）

给定函数项 `f :: A ⇒ B` 和参数项 `a :: A`，可构成函数应用 `f a`。构造器为 `Comb(f, a)`。

函数应用**左结合**：`f a b` 表示 `(f a) b`，而非 `f (a b)`。对于二元运算 `plus x y`，实际结构是 `(plus x) y`--`plus x` 是 `plus` 的部分应用，本身是一个 `nat ⇒ nat` 的函数。

给定项 `f t₁ t₂ … tₙ`，`strip_comb` 返回 `(f, [t₁, …, tₙ])`。`head` 返回 `f`，`args` 返回 `[t₁, …, tₙ]`。

### 2.3 抽象（Abstraction）

**λ 抽象** `λx. t` 表示一个函数：输入 `x`，输出 `t`。构造器为 `Abs(x, T, body)`，其中 `x` 是建议的绑定变量名（仅用于打印），`T` 是绑定变量的类型，`body` 是函数体。

**绑定变量的名字不重要**：`λx. x + 2` 与 `λy. y + 2` 表示同一函数。称二者 **α-等价**。

### 2.4 de Bruijn 索引

为了快速判断两个项是否 α-等价，holpy 使用 **de Bruijn 索引**表示绑定变量。绑定变量在原则上无名，引用时用 `Bᵢ`，其中 `i` 是从引用位置到绑定它的 λ 的"深度"（从 0 开始数中间隔了多少层 λ）。

例如：
- `λx. x + 2` 表示为 `λ_. B₀ + 2`（`x` 的引用与绑定它的 λ 之间隔 0 层）。
- `λx. λy. x + y` 表示为 `λ_. λ_. B₁ + B₀`（`x` 隔 1 层，`y` 隔 0 层）。

在 holpy 中，`Abs` 的 `var_name` 字段只是**建议名**（用于打印和发明新变量时的起点），`var_T` 是**有意义的**（不同类型给出不同的项），`body` 中的绑定变量用 `Bound(n)` 引用。

### 2.5 β-变换

函数应用 `(λx. t₁) t₂` 可通过 **β-变换**化简为 `t₁[t₂/x]`（将 `t₂` 代入 `t₁` 中的 `x`）。

β-变换不自动传播：`Comb` 构造器只是组合函数与参数，不做求值。需要显式调用 β-变换。**β-归一化**（beta normalization）是反复进行 β-变换直到无法再进行，得到 β-标准形。

### 2.6 常用运算符

许多常用运算符是二元函数：
- 加法 `plus :: nat ⇒ nat ⇒ nat`，项 `x + y` 实际是 `plus x y`。
- 合取 `conj :: bool ⇒ bool ⇒ bool`，项 `A ∧ B` 实际是 `conj A B`。
- 相等 `equals :: 'a ⇒ 'a ⇒ bool`，可接受任意类型的两个参数（类型变量 `'a` 被实例化）。
- 布尔相等打印为 `⟷`（if-and-only-if），但内部仍是 `equals`。

打印时按运算符优先级与结合性显示为中缀形式。逻辑运算符 `∧`/`∨` 向右结合，`⟶` 向右结合，`∧` 优先于 `∨`，`∨` 优先于 `⟶`。

## 3. 量词

谓词逻辑在命题逻辑之上引入两个量词。

### 3.1 全称量词

`∀x. P x` 表示"对所有 x，P x 成立"。在高阶逻辑中，`∀` 是类型为 `('a ⇒ bool) ⇒ bool` 的常量：它接受一个谓词 `P :: 'a ⇒ bool`，返回布尔值。

高阶逻辑与一阶逻辑的关键区别：**量词的绑定变量可以是任意类型**，包括函数类型。一阶逻辑中绑定变量只能取值于"对象"。

### 3.2 存在量词

`∃x. P x` 表示"存在 x 使得 P x 成立"。`∃` 类型同为 `('a ⇒ bool) ⇒ bool`。

`∃!x. P x`（存在唯一）是 `∃x. P x ∧ (∀y. P y ⟶ y = x)` 的缩写。

### 3.3 多参数与交替

`∀` 和 `∃` 可接受多个参数：`∀x y. P x y` 等价于 `∀x. ∀y. P x y`。

量词可交替：`∀x. ∃y. y > x`（对每个 x 存在更大的 y，真）与 `∃y. ∀x. y > x`（存在大于一切 x 的 y，假）含义不同。

## 4. Sequent 与自然演绎

### 4.1 Sequent

一个 **sequent** 由一组假设（antecedents）和一个结论（consequent）组成，写作：

```
A₁, …, Aₙ ⊢ C
```

每个假设和结论都是 `bool` 类型的项。假设视为**集合**（无序、去重），但常按元组书写以方便。

### 4.2 自然演绎

**自然演绎**（natural deduction）是一种描述证明的方式：每步证明产生一个 sequent，通过**推理规则**（deduction rules）从前面的 sequent 得到新的 sequent。

推理规则用图形表示：

```
  前提₁  …  前提ₖ
─────────────────  规则名
      结论
```

横线上方是输入，下方是输出。所有规则中的变量可替换为任意合适类型的项。

### 4.3 证明的书写格式

证明写成编号的步骤列表，每行一个 sequent：

```
0. A ⊢ A                              by assume A
1. A ⊢ A ∧ A                          by ...
2. ⊢ A ⟶ A ∧ A                        by implies_intr A from 1
```

每行包含：编号、得到的 sequent、`by` 后是规则名、参数、`from` 后是输入 sequent 的编号。后续章节的 `ProofTerm` 与 `.pyhol` 证明都遵循这一格式。
## 5. 原始推理规则

高阶逻辑的推理规则由一组**原始推理规则**（primitive deduction rules）定义。这些规则是逻辑的根基，是唯一能"凭空"构造定理的入口。holpy 的内核实现了 15 条原语（见 `02_kernel.md`）。此处先介绍其逻辑含义。

### 5.1 假设

```
─────────  assume
  A ⊢ A
```

对任意布尔项 `A`，`A ⊢ A` 成立。

### 5.2 蕴含

**引入**（`implies_intr`）：

```
  Γ, A ⊢ B
─────────────  implies_intr A
  Γ ⊢ A ⟶ B
```

从 `A` 能推出 `B`，则 `A ⟶ B` 成立。`A` 从假设中移除。

**消除**（`implies_elim`，即假言推理 MP）：

```
  Γ₁ ⊢ A ⟶ B    Γ₂ ⊢ A
─────────────────────  implies_elim
      Γ₁ ∪ Γ₂ ⊢ B
```

### 5.3 等式

等式由四条性质刻画。

**自反**（`reflexive`）：
```
─────────────  reflexive
  ⊢ x = x
```

**对称**（`symmetric`）：
```
  Γ ⊢ x = y
─────────────  symmetric
  Γ ⊢ y = x
```

**传递**（`transitive`）：
```
  Γ₁ ⊢ x = y    Γ₂ ⊢ y = z
─────────────────────────  transitive
      Γ₁ ∪ Γ₂ ⊢ x = z
```

**同余**（`combination`）：
```
  Γ₁ ⊢ f = g    Γ₂ ⊢ x = y
─────────────────────────  combination
      Γ₁ ∪ Γ₂ ⊢ f x = g y
```

### 5.4 布尔等式

**等价引入**（`equal_intr`）：

```
  Γ₁ ⊢ A ⟶ B    Γ₂ ⊢ B ⟶ A
─────────────────────────  equal_intr
      Γ₁ ∪ Γ₂ ⊢ A = B
```

证明 `A = B`（A、B 为布尔）可通过证明两个方向的蕴含。

**等价消除**（`equal_elim`）：

```
  Γ₁ ⊢ A = B    Γ₂ ⊢ A
─────────────────────  equal_elim
      Γ₁ ∪ Γ₂ ⊢ B
```

### 5.5 替换

**类型替换**（`subst_type`）：对类型变量赋值 `σ`，

```
  Γ ⊢ B
──────────────  subst_type σ
  Γ[σ] ⊢ B[σ]
```

**项替换**（`substitution`）：对项变量（含类型变量）赋值 `σ`，

```
  Γ ⊢ B
──────────────  substitution σ
  Γ[σ] ⊢ B[σ]
```

已证定理中的变量可替换为任意合适类型的项，定理仍成立。这是复用已证定理的关键。

### 5.6 β-变换

```
─────────────────────────────  beta_conv
  ⊢ (λx. t₁) t₂ = t₁[t₂/x]
```

### 5.7 抽象

```
  Γ ⊢ t₁ = t₂
──────────────────────────  abstraction x
  Γ ⊢ (λx. t₁) = (λx. t₂)
```

要求 `x` 不在 `Γ` 中自由出现。这是证明两个 λ 项相等的规则。

### 5.8 全称量词

**引入**（`forall_intr`）：

```
  Γ ⊢ t
──────────────────  forall_intr x
  Γ ⊢ ∀x. t
```

要求 `x` 不在 `Γ` 中自由出现。这是"对任意 x 成立"的形式化：假设新变量 `x`，证明 `t`，则 `∀x. t`。

**消除**（`forall_elim`）：

```
  Γ ⊢ ∀x. t
────────────────  forall_elim s
  Γ ⊢ t[s/x]
```

`∀x. P x` 成立则对任意合适类型的 `s`，`P s` 成立。`s` 的类型须匹配绑定变量。

## 6. 命题逻辑

命题逻辑有四个运算符：合取 `∧`、析取 `∨`、蕴含 `⟶`、否定 `¬`。蕴含规则已在 §5.2 给出。其余三个的规则以公理形式引入。

### 6.1 合取

- `conjI`：`A ⟶ B ⟶ A ∧ B`（引入）
- `conjD1`：`A ∧ B ⟶ A`（消除一）
- `conjD2`：`A ∧ B ⟶ B`（消除二）

**例**：证明 `A ∧ B ⟶ B ∧ A`。

```
0. A ∧ B ⊢ A ∧ B                    by assume A ∧ B
1. A ∧ B ⊢ A                        by apply_theorem conjD1 from 0
2. A ∧ B ⊢ B                        by apply_theorem conjD2 from 0
3. A ∧ B ⊢ B ∧ A                    by apply_theorem conjI from 2, 1
4. ⊢ A ∧ B ⟶ B ∧ A                  by implies_intr A ∧ B from 3
```

### 6.2 析取

- `disjI1`：`A ⟶ A ∨ B`（引入一）
- `disjI2`：`B ⟶ A ∨ B`（引入二）
- `disjE`：`A ∨ B ⟶ (A ⟶ C) ⟶ (B ⟶ C) ⟶ C`（消除，即分情况分析）

`disjE` 的含义：若 `A ∨ B` 成立，要证 `C`，只需分别从 `A` 证 `C` 和从 `B` 证 `C`。

**例**：证明 `A ∨ B ⟶ B ∨ A`。

```
0. A ∨ B ⊢ A ∨ B                    by assume A ∨ B
1. A ⊢ A                            by assume A
2. A ⊢ B ∨ A                        by apply_theorem disjI2 from 1
3. ⊢ A ⟶ B ∨ A                      by implies_intr A from 2
4. B ⊢ B                            by assume B
5. B ⊢ B ∨ A                        by apply_theorem disjI1 from 4
6. ⊢ B ⟶ B ∨ A                      by implies_intr B from 5
7. A ∨ B ⊢ B ∨ A                    by apply_theorem disjE from 0, 3, 6
8. ⊢ A ∨ B ⟶ B ∨ A                  by implies_intr A ∨ B from 7
```

### 6.3 否定

否定与矛盾 `false` 紧密相关。可定义 `¬A` 为 `A ⟶ false`。

- `negI`：`(A ⟶ false) ⟶ ¬A`（引入）
- `negE`：`¬A ⟶ A ⟶ false`（消除）

**例**：证明 `A ⟶ ¬¬A`。

```
0. A ⊢ A                            by assume A
1. ¬A ⊢ ¬A                          by assume ¬A
2. A, ¬A ⊢ false                    by apply_theorem negE from 1, 0
3. A ⊢ ¬A ⟶ false                   by implies_intr ¬A from 2
4. A ⊢ ¬¬A                          by apply_theorem negI from 3
5. ⊢ A ⟶ ¬¬A                        by implies_intr A from 4
```

### 6.4 经典逻辑

以上规则构成直觉主义逻辑。要证明所有经典有效的命题，还需两条公理：

- `falseE`：`false ⟶ A`（爆炸原理：从矛盾可证任意命题）
- `classical`：`A ∨ ¬A`（排中律：经典逻辑与直觉主义的分界）

**例**：证明 `¬¬A ⟶ A`（需要排中律与爆炸原理）。

```
0. ¬¬A ⊢ ¬¬A                        by assume ¬¬A
1. ⊢ A ∨ ¬A                         by apply_theorem classical
2. A ⊢ A                            by assume A
3. ⊢ A ⟶ A                          by implies_intr A from 2
4. ¬A ⊢ ¬A                          by assume ¬A
5. ¬A, ¬¬A ⊢ false                  by apply_theorem negE from 0, 4
6. ¬A, ¬¬A ⊢ A                      by apply_theorem falseE from 5
7. ¬¬A ⊢ ¬A ⟶ A                     by implies_intr ¬A from 6
8. ¬¬A ⊢ A                          by apply_theorem disjE from 1, 3, 7
9. ⊢ ¬¬A ⟶ A                        by implies_intr ¬¬A from 8
```

## 7. 谓词逻辑

### 7.1 全称量词的规则

已在 §5.8 给出原语级的 `forall_intr`/`forall_elim`。

**例**：证明 `(∀x. P x ∧ Q x) ⟶ (∀x. P x) ∧ (∀x. Q x)`。

```
0. ∀x. P x ∧ Q x ⊢ ∀x. P x ∧ Q x    by assume
1. ∀x. P x ∧ Q x ⊢ P x ∧ Q x        by forall_elim x from 0
2. ∀x. P x ∧ Q x ⊢ P x              by apply_theorem conjD1 from 1
3. ∀x. P x ∧ Q x ⊢ Q x              by apply_theorem conjD2 from 1
4. ∀x. P x ∧ Q x ⊢ ∀x. P x          by forall_intr x from 2
5. ∀x. P x ∧ Q x ⊢ ∀x. Q x          by forall_intr x from 3
6. ∀x. P x ∧ Q x ⊢ (∀x. P x) ∧ (∀x. Q x)  by apply_theorem conjI from 4, 5
7. ⊢ (∀x. P x ∧ Q x) ⟶ (∀x. P x) ∧ (∀x. Q x)  by implies_intr from 6
```

### 7.2 存在量词的规则

存在量词不是原语，其规则以公理形式引入：

- `exI`：`P a ⟶ (∃a1. P a1)`（引入：`P a` 成立则存在见证）
- `exE`：`(∃a. P a) ⟶ (∀a. P a ⟶ C) ⟶ C`（消除：从 `∃a. P a` 证明 `C`，只需取任意 `a` 假设 `P a` 证 `C`）

`exE` 较为微妙：应用时 `C` 被实例化为当前目标，目标从 `C` 变为 `∀a. P a ⟶ C`，随后立即 `forall_elim` + `implies_elim` 得到新变量 `a` 与假设 `P a`，结论仍是 `C`。

**例**：证明 `(∃x. P x ∧ Q x) ⟶ (∃x. P x) ∧ (∃x. Q x)`。

```
0. ∃x. P x ∧ Q x ⊢ ∃x. P x ∧ Q x    by assume
1. P x ∧ Q x ⊢ P x ∧ Q x             by assume
2. P x ∧ Q x ⊢ P x                   by apply_theorem conjD1 from 1
3. P x ∧ Q x ⊢ ∃x. P x               by apply_theorem exI from 2
4. P x ∧ Q x ⊢ Q x                   by apply_theorem conjD2 from 1
5. P x ∧ Q x ⊢ ∃x. Q x               by apply_theorem exI from 4
6. P x ∧ Q x ⊢ (∃x. P x) ∧ (∃x. Q x) by apply_theorem conjI from 3, 5
7. ⊢ P x ∧ Q x ⟶ (∃x. P x) ∧ (∃x. Q x)  by implies_intr from 6
8. ⊢ ∀x. P x ∧ Q x ⟶ (∃x. P x) ∧ (∃x. Q x)  by forall_intr x from 7
9. ∃x. P x ∧ Q x ⊢ (∃x. P x) ∧ (∃x. Q x)   by apply_theorem exE from 0, 8
10. ⊢ (∃x. P x ∧ Q x) ⟶ (∃x. P x) ∧ (∃x. Q x)  by implies_intr from 9
```

### 7.3 量词交替

**例**：证明 `(∃x. ∀y. R x y) ⟶ (∀y. ∃x. R x y)`。

```
0. ∃x. ∀y. R x y ⊢ ∃x. ∀y. R x y    by assume
1. ∀y. R x y ⊢ ∀y. R x y             by assume
2. ∀y. R x y ⊢ R x y                 by forall_elim y from 1
3. ∀y. R x y ⊢ ∃x. R x y             by apply_theorem exI from 2
4. ∀y. R x y ⊢ ∀y. ∃x. R x y         by forall_intr y from 3
5. ⊢ (∀y. R x y) ⟶ (∀y. ∃x. R x y)   by implies_intr from 4
6. ⊢ ∀x. (∀y. R x y) ⟶ (∀y. ∃x. R x y)  by forall_intr x from 5
7. ∃x. ∀y. R x y ⊢ ∀y. ∃x. R x y     by apply_theorem exE from 0, 6
8. ⊢ (∃x. ∀y. R x y) ⟶ (∀y. ∃x. R x y)  by implies_intr from 7
```

## 8. 归纳类型与递归定义

### 8.1 归纳类型

自然数通过**归纳类型**（datatype）定义，遵循 Peano 算术：

```
datatype nat =
  zero
  Suc (n :: nat)
```

两个构造器 `zero :: nat` 与 `Suc :: nat ⇒ nat` 生成所有自然数：`zero`、`Suc zero`、`Suc (Suc zero)`、…

归纳类型自动产生：
- **inject**（单射性）：`Suc m = Suc n ⟶ m = n`。
- **distinct**（互异性）：`zero ≠ Suc n`。
- **归纳定理**（induction）：要证 `∀x. P x`，只需证 `P zero` 和 `∀n. P n ⟶ P (Suc n)`。

### 8.2 递归定义

加法通过**递归定义**（fun）给出：

```
fun plus :: nat ⇒ nat ⇒ nat
  0 + n = n
  Suc m + n = Suc (m + n)
```

每条等式作为一条**重写规则**定理（如 `nat_plus_def_1`、`nat_plus_def_2`），可用于化简。

乘法类似：

```
fun times :: nat ⇒ nat ⇒ nat
  0 * n = 0
  Suc m * n = n + m * n
```

### 8.3 二进制表示

`Suc` 表示指数级昂贵。实践用**二进制表示**：`zero`、`one`、`bit0`（翻倍）、`bit1`（翻倍加一）。例如 `10 = bit0 (bit1 (bit0 one))`。

大于一的数用 `of_nat :: nat ⇒ nat`（自然数上的恒等函数，为与其他数系一致而设）应用到二进制项表示。

### 8.4 归纳证明示例

**例**：证明 `n + 0 = n`（基础情况由定义直接给出，但 `n + 0` 需归纳）。

```
0. ⊢ 0 + 0 = 0                       by rewrite nat_plus_def_1
1. n + 0 = n ⊢ n + 0 = n             by assume
2. ⊢ Suc n + 0 = Suc (n + 0)         by rewrite nat_plus_def_2
3. n + 0 = n ⊢ Suc n + 0 = Suc n     by rewrite 2 with 1
4. ⊢ n + 0 = n ⟶ Suc n + 0 = Suc n   by implies_intr from 3
5. ⊢ ∀n. n + 0 = n ⟶ Suc n + 0 = Suc n  by forall_intr n from 4
6. ⊢ n + 0 = n                       by apply_theorem nat_induct from 0, 5
```

## 9. 与其他系统的关系

### 9.1 与一阶逻辑的区别

高阶逻辑与一阶逻辑的核心区别：
1. 量词的绑定变量可为任意类型（含函数类型）。
2. 谓词本身是一等公民（可作为参数、返回值）。
3. 可表达高阶性质（如"对所有谓词 P，…"）。

### 9.2 经典 vs 直觉主义

不含 `falseE` 与 `classical` 的子系统是直觉主义逻辑：只能证明构造性成立的命题。加入排中律 `classical` 后得到经典逻辑，可证明所有语义有效的命题。holpy 默认采用经典逻辑（`classical` 是公理）。

### 9.3 与简单类型 λ 演算的关系

高阶逻辑可视为**简单类型 λ 演算**（simply-typed lambda calculus）加上逻辑常量（`equals`、`implies`、`all` 等）与推理规则。类型系统保证项的良构性，λ 演算提供函数表示，逻辑常量与规则定义证明。

---

**下一章**：[`02_kernel.md`](02_kernel.md) -- holpy 如何用 Python 实现上述类型、项、定理与 15 条原语。
