# holpy Z3 证明重建：实现现状与局限

> 本文档描述已交付的 Z3 证明重建系统的**实际状态**（不再是设计规划）。
> 每一节都对应仓库中已提交、已测试的代码。

## 1. 总览

holpy 的 Z3 证明重建把 Z3 4.x 给出的证明 DAG 逐步翻译成核内 ProofTerm（LCF 风格，
参照 Böhme/Weber 的 Isabelle SMT 重构架构），最终把"反证 refutation"闭合回
原定理陈述。每一步都由 holpy kernel 检查；重建结果可以用
`theory.check_proof(pt.export())` 做核级验收。

入口与工作流（`solvers/z3wrapper.py` + `solvers/proofrec.py`）：

```
陈述 t（自由 schematic 变元 = 任意常量，无需量化）
  → solve_core：strip_all_implies 拆成假设 A1..An + 结论 C，
    断言 [A1..An, ¬C]，要求 unsat（solve_and_proof 返回证明 DAG）
  → proofrec.proofrec：DAG 逐节点重建（translate / method dispatch）
  → close_sequent：把带假设的 ⊢ false 闭合为 ⊢ A1 ⟹ … ⟹ An ⟹ C
  → solve_and_reconstruct(t)：一站式，返回 ⊢ t 本身
```

## 2. 已实现

### 2.1 翻译覆盖（双向）

- **类型**：nat（全程擦除为 int）、int、real、bool、函数类型
  （Z3 ArraySort ↔ holpy 函数类型）、数组 Select/Store ↔ 函数应用/fun_upd。
- **算子**：+ − × uminus、实数除、整数 DIV/MOD、power（nat/int/real 指数）、
  of_int/of_nat、min/max/abs、ITE、量词 ∀/∃、相等/比较、全部布尔连接词、
  distinct、TO_REAL。发送侧用底层 `Z3_mk_power` 构造整数幂节点
  （z3py 的 `**` 会产生 Real 排序异构节点，污染整数幂证明）。
- **除零语义钉定**：SMT-LIB 中除零未定义，holpy 侧 `n DIV 0 = 0`、
  `n MOD 0 = n`；按实例用 ground implication 钉住，对 refutation 可靠。

### 2.2 判定网（覆盖 Z3 rewriter 278 条规则中的 ~177 条可判定规则）

- **SAT 网** `_sat_net`：Tseitin 编码 + solve_cnf（sat.pyhol），命题层完备。
- **算术归一网** `_arith_norm_net`：int 用 omega（`omega_simp_full_conv`）、
  real 用 `real_eval_conv` 常量折叠；两侧规范形相等即闭合。
- **原子布尔网** `_atom_bool_net`：`atom ⟷ true/false`（含否定包裹、¬/¬ 同余、
  双重否定、线性比较原子直接证明 `_prove_comp`、闭式等式原子裁决）。
- **数值求值** `_ground_eval`：闭式等式由受信任的 `nat_eval`/`int_eval` 宏
  求值闭合（已扩展 power/DIV/MOD，指数上限 4096 防炸）。

### 2.3 schematic 层（对应 ~117 条不可判定改写规则）

- `library/smt.pyhol` r001–r156（含布尔代数、整数/实数环律、零积、mul_ge_0
  情形分裂、平方非负、比较朝向、字面折叠等）+ `SCHEMATIC_EXTRA` 63 个库名，
  约 210 个可匹配名字。
- **条件式 schematic** `schematic_rules_rewr_cond`：形如 `h ⟹ a = b` 的定理
  （如 fun_upd_other），假设由判定网 discharge，失败则跳过，保证无 gap。

### 2.4 Sequent 闭合（真实定理端到端的关键）

- **`close_sequent`**（proofrec.py）：把重建出的 `⊢ false`（假设 = 断言的
  z3 规范形）闭合为 `⊢ A1 ⟹ … ⟹ An ⟹ C`：
  1. 假设与 sequent 片段按**规范形**双射匹配——规范链 = 布尔字面折叠
     （r155/r156）+ 等式朝向（`eq_num_swap_conv`，用对称律 r001）+
     ≥/≤ 朝向（r153/r154）+ 比较归一 + `proplogic.norm_full`，双趟到不动点；
  2. 内层 `imp_false_iff + double_neg` 把 `¬C ⟹ false` 翻成 `⊢ C`；
  3. 向外逐层 `implies_intr` discharge 假设；
  4. 通过"两侧规范形相等"的 iff 桥接回原始陈述（终止安全，不用膨胀型
     replace 重写）。
- **`z3wrapper.solve_and_reconstruct(t)`**：求解 → 重建 → 闭合 → 桥接回
  `norm_term` 之前的原陈述形状，返回 `⊢ t`。
- **真实定理闭环验证** `solvers/tests/proofrec_real_theorems.py`：
  10 条真实库定理 **9 条 CLOSED**（int_add_comm、int_add_assoc、
  real_add_comm、r146、r149、r151、r152、r155、r156——最后一步全部
  断言"重建结论与库中存储陈述逐字相等 + check_proof 通过"）。
  这意味着这类定理的空证明（trusted）可以被真正的 z3 证明 + 核内重建取代。

### 2.5 测试基建（全部带硬超时）

| 工具 | 内容 | 结果 |
| --- | --- | --- |
| `solvers/tests/proofrec_corpus.py` | 32 目标回归 runner；每目标独立子进程 + 20s 硬杀 + 全局预算 + xfail 记账 | 28 PASS + 4 XFAIL |
| `solvers/tests/proofrec_smoke_test.py` | 10 目标冒烟，断言 rule≠sorry、无 gap、**核级 check_proof** | 10/10 |
| `solvers/tests/proofrec_unit_test.py` | 6 个 z3-free 单元测试（occurs/数值求值/原子网/条件式 schematic/命题网） | 6/6 |
| `solvers/tests/proofrec_real_theorems.py` | 真实定理端到端闭环 | 9 CLOSED + 1 XFAIL |
| pytest 全套 | 回归基线 | 62 passed, 0 failed |

语料覆盖类别：prop 3、int 6、real 3、divmod 6（含除零钉定、DIV/MOD 1、
数词求值）、power 5（4 xfail）、of_int 2、quant 2、array 3、nonlin 2。

## 3. 局限（诚实清单）

1. **整数幂（已定位，未做）**：Z3 内部把整数幂求值走 ToReal/实数幂路由，
   产生的证明步翻译到 holpy 需要"实数幂翻译层 + real power 库引理"，
   目前留 gap（语料 4 个 xfail、int_power_1 xfail）。实数幂（pow4）正常。
2. **内层量词闭合**：量词出现在目标内部、且 z3 用 skolem 化 + 情形分裂证明时
   （假设是含 skolem 常量的分支原子），skolem → ∀-intro 的推广闭合未实现。
   对 schematic 定理（自由变元直送、不量化）已绕开此问题；语料 quant 类
   （∀ 在蕴涵前件）正常。
3. **数组 th-lemma**：数组公理实例化的 th-lemma 重建机制缺失；当前靠
   fun_upd schematic + 条件式 discharge 覆盖常见情形（语料 array 3/3）。
4. **非线性**：无实代数判定程序（real_th_lemma 仅线性）；非线性目标依赖
   Z3 的改写形状 + r149/r151/r152 情形分裂 schematic，不能保证闭合。
5. **branch_and_bound**（simplex.py）：整数 simplex 兜底，2000 节点上限，
   未处理无界区域的完全性；契约 = 耗尽时返回根树由 `branch_and_bound_pt`
   从叶子重解推导反证。
6. **不支持的理论**：位向量、浮点、字符串/序列（holpy 无对应库，
   z3wrapper 不翻译）。
7. **omega 已知 bug**：常量相消不等式（如 `1 + x ≤ x`）会崩，
   `_refute_atom` 已用 simplex 兜底。
8. **规范形不匹配时诚实回落**：close_sequent 匹配失败会原样返回
   `⊢ false`（调用方的精确比对会发现），不会产生错误证明。

## 4. 运行方式

```bash
# 语料回归（仓库根目录）
PROOFREC_TIMEOUT=20 python solvers/tests/proofrec_corpus.py [类别...]
# 真实定理闭环
PROOFREC_TIMEOUT=40 python solvers/tests/proofrec_real_theorems.py
# 冒烟 + 单元（注意：需从仓库根以 unittest discover 运行，直接当脚本跑
# 会因 framework 不在 sys.path 报 ModuleNotFoundError）
python -m unittest discover -s solvers/tests -p "proofrec_*test.py"
# 全套 pytest
python -m pytest solvers/tests -q
```

z3 4.16 实测环境：Python 3.12，Windows。

## 5. 参考文献

- Sascha Böhme and Tjark Weber, "Fast LCF-Style Proof Reconstruction for Z3"
  （Isabelle/HOL + HOL4 方向的 LCF 风格 Z3 证明重建经典论文）。
  holpy 的重建沿用其总体架构：Z3 证明 DAG 逐节点翻译为核内定理、
  命题/一阶步骤用原语与示意图定理组合建模、理论步骤（rewrite/th-lemma）
  用示意图定理 + 化简器 + 算术判定过程承接。
  论文原文曾以 `Z3recpaper.md` 存档于仓库根目录，因本文档已是实现现状的
  权威描述、代码头注释（`solvers/proofrec.py`）亦保留引用，存档正文不再保留，
  需要时按标题自行检索论文。
