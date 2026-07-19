# 第一层：内核原语

## 概述

内核是 HOL 系统的可信计算基。所有证明最终必须归结到这 15 条原始规则。内核之外的任何代码（宏、策略、转换、方法）如果出错，都不会破坏系统 soundness——因为它们最终都要经过内核验证。

## 数据结构

### Type（类型）

```
STVar(name)     — 模式类型变量（可实例化，?'a）
TVar(name)      — 固定类型变量（不可实例化，'a）
TConst(name, *) — 类型常量（bool, fun, nat, list, real, ...）
```

辅助构造：`TFun(a, b)` = `a => b`（函数类型）

### Term（项）

```
SVar(name, T)  — 模式变量（可实例化）
Var(name, T)   — 固定变量
Const(name, T) — 理论常量
Comb(f, x)     — 函数应用 f x
Abs(n, T, body)— Lambda 抽象 %x::T. body（de Bruijn）
Bound(n)       — de Bruijn 索引变量
```

de Bruijn 索引：`Bound(0)` 指向最内层绑定。`Abs("x", T, Bound(0))` = `%x. x`。

### Thm（定理）

```python
class Thm:
    prop: Term        # 命题
    hyps: Tuple[Term] # 假设集合
```

表示 `A1, ..., An |- C`。只能通过原始规则构造，不能直接 `Thm(prop, *hyps)`（运行时不检查，但 check_proof 会验证）。

## 15 条原始规则

### 假设与蕴含

| 规则 | 签名 | 说明 |
|------|------|------|
| `assume(A)` | `A \|- A` | 假设 |
| `implies_intr(A, th)` | `A \|- B` → `\|- A --> B` | 蕴含引入 |
| `implies_elim(th1, th2)` | `\|- A-->B, \|- A` → `\|- B` | 蕴含消除（MP） |

### 等式

| 规则 | 签名 | 说明 |
|------|------|------|
| `reflexive(x)` | `\|- x = x` | 自反性 |
| `symmetric(th)` | `\|- x=y` → `\|- y=x` | 对称性 |
| `transitive(th1, th2)` | `\|- x=y, \|- y=z` → `\|- x=z` | 传递性 |
| `combination(th1, th2)` | `\|- f=g, \|- x=y` → `\|- f x = g y` | 组合（同余） |
| `equal_intr(th1, th2)` | `\|- A-->B, \|- B-->A` → `\|- A=B` | 等价引入 |
| `equal_elim(th1, th2)` | `\|- A=B, \|- A` → `\|- B` | 等价消除 |

### 替换

| 规则 | 签名 | 说明 |
|------|------|------|
| `substitution(inst, th)` | 项替换 | 用 Inst 替换模式变量 |
| `subst_type(tyinst, th)` | 类型替换 | 用 TyInst 替换模式类型变量 |

### Lambda 演算

| 规则 | 签名 | 说明 |
|------|------|------|
| `beta_conv(t)` | `\|- (%x. t1) t2 = t1[t2/x]` | Beta 转换 |
| `abstraction(x, th)` | `\|- t1=t2` → `\|- (%x.t1) = (%x.t2)` | 抽象 |

### 量词

| 规则 | 签名 | 说明 |
|------|------|------|
| `forall_intr(x, th)` | `\|- t` → `\|- !x. t` | 全称引入（x 不在 hyps 中） |
| `forall_elim(s, th)` | `\|- !x. t` → `\|- t[s/x]` | 全称消除 |

## 可用的逻辑常量

内核初始化时注册：

```
equals  :: 'a => 'a => bool   （等式）
implies :: bool => bool => bool（蕴含）
all     :: ('a => bool) => bool（全称量词）
```

其他常量（`conj`, `disj`, `neg`, `exists`, `false`, `true` 等）通过 theory extension 添加。

## ProofTerm（证明项）

树形证明表示，比线性 Proof 更方便构造：

```python
# 构造
pt = ProofTerm.assume(A)           # A |- A
pt = ProofTerm.reflexive(x)        # |- x = x
pt = ProofTerm.theorem('conjI')    # |- ?A --> ?B --> ?A & ?B
pt = ProofTerm.sorry(th)           # 创建 gap

# 操作
pt.implies_intr(A)                 # 蕴含引入
pt.implies_elim(pt2)               # 蕴含消除
pt.symmetric()                     # 对称
pt.transitive(pt2)                 # 传递
pt.equal_intr(pt2)                 # 等价引入
pt.substitution(inst)              # 替换
pt.subst_type(tyinst)              # 类型替换
pt.on_prop(*convs)                 # 对命题应用转换

# 导出
pt.export()                        # 转为线性 Proof
pt.th                              # 获取结果 Thm
pt.gaps                            # 获取所有 sorry gap
```

## Theory（理论）

全局理论状态，存储：

```python
theory.thy.data['type_sig']    # 类型签名 {name: arity}
theory.thy.data['term_sig']    # 常量签名 {name: Type}
theory.thy.data['theorems']    # 定理 {name: Thm}
theory.thy.data['attributes']  # 属性 {name: (attr, ...)}
theory.thy.data['overload']    # 重载常量 {name: True}
theory.thy.data['thm_status']  # 证明状态 {name: status}
```

## 宏（Macro）

派生证明方法，有信任级别：

```python
@register_macro('my_macro')
class MyMacro(Macro):
    level = 1  # 信任级别（越低越可信）

    def eval(self, args, prevs) -> Thm:
        # 快速计算（信任路径）
        ...

    def get_proof_term(self, args, prevs) -> ProofTerm:
        # 详细证明（可展开检查）
        ...
```

- `level <= check_level`：直接 eval，信任结果
- `level > check_level`：展开为原始步骤，逐步验证
