# 证明重建参考纪要（from sat/ and smt/veriT/）

> 本文件总结了已删除的 `sat/`（zChaff）与 `smt/veriT/`（veriT）两套
> 证明重建实现中的精华，供继续开发 Z3 证明重建（`prover/proofrec.py`）参考。
>
> 三套重建对比：
>
> | 实现 | 状态 | 特点 |
> |---|---|---|
> | veriT（已删） | 完整链路 | 证明**每条 step 带规则名**，HOL 侧一规则一宏（level 1 可展开校验） |
> | zChaff（已删） | 完整链路 | Tseitin 编码携带等价证明 + 消解/蕴含/冲突证据全部重建 |
> | Z3（`prover/proofrec.py`） | 半成品 | `rewrite` 规则是黑盒，无法逐规则重建；9 处 NotImplementedError |

## 1. veriT 重建架构（规则名驱动）

链路：`veriT` 可执行文件（`--proof-*` 参数出证明）→ 解析

```
subprocess veriT --proof-prune --proof-with-sharing --proof-merge --proof=- f.smt2
  ↓ ≪proof text≫
proof_parser  （Lark grammar → Assume/Step/Anchor 命令流）
  ↓
proof_rec: ProofReconstruction
  ↓
verit_macro.py 每个 veriT 规则一个 @register_macro(name, level=1) 宏
  ↓
HOL ProofTerm（可 check_proof 成 15 原语）── 这是「可重验」的关键
```

- **命令模型**（`command.py`）：`Assume`（假设，当步的支撑边时）、`Step`（规则名 + 结论 + 输入引用）、`Anchor`（无需证明的蕴含锚点）。输入引用构成一个 DAG（支持 sharing）。
- **规则名 → HOL 宏**（`verit_macro.py`，约 8800 行，80 余宏，全部 `level=1`）：
  - 命题：`verit_not_or`/`verit_not_and`/`verit_not_not`/`verit_implies`/`verit_and_pos`/`verit_or_pos`/`swap_disj_to_front`/`combine_disj_clauses`
  - 等式：`verit_equiv1/2`、`verit_eq_reflexive/transitive/congruent(_pred)`、`verit_distinct_elim`
  - if-then-else：`verit_ite1/2`、`verit_not_ite1/2`、`verit_bind`
  - 量词：`verit_forall_inst`、`verit_sko_ex`/`verit_sko_forall`（**Skolem 化在 HOL 的处理**）、`verit_onepoint`、`verit_qnt_cnf`/`verit_qnt_join`/`verit_qnt_rm_unused`
  - 理论：`verit_la_rw_eq`、`verit_la_disequality`、`verit_la_generic`、`verit_norm_lia`/`verit_norm_lra`/`verit_round_lia`
- **conv 工具**（`verit_conv.py`）：LIA/LRA 归一化（`norm_lia_conv`/`norm_lra_conv`，把项化为规范多项式）、CNF 转换（`cnf_conv`/`combine_clause*`）、De Morgan（`deMorgan_*`）、量词（`onepoint_forall_conv`/`exists_forall_conv`/`forall_elim_conv`/`exists_elim_conv`/`qnt_rm_unused_conv`）、`lt_ands_to_leq` 等。
- **通用线性算术宏**（`th-lemma` 的建块）：
  - 归约链：目标不等式 `x ≥ 0` 先 `neg` 反号、`norm_lia` 化多项式、约化到矛盾。
  - `verit_la_generic` 输入：一组线性事实假设 + 目标线性结论，重建为 HOL proof term，等价于 Z3 的 `th-lemma` step。
- **Node 支持**：按 anchor/事实，但主要按规则名优先。

## 2. zChaff 重建（Tseitin 编码 + 冲突证据）

链路：`tseitin.encode` → CNF → `.cnf` → zchaff.exe → trace → 重建：

```
tseitin.encode(t)          # 携带等价证明 encode_pt（t ⟷ CNF），非丢编码
  ↓
zchaff.exe（DPLL，输出 resolve_trace：CL / VAR / CONF）
  ↓
- CL（Resolvent）   : 记录消解出；重建 = 循环 resolution() 合并
- VAR（ImpliedVar） : 单元蕴含；重建 = DisjForceMacro（unit propagation 证明）
- CONF（Conflict）  : 空子句；重建 = DisjFalseMacro（证冲突子句全假）
  ↓
DisjForceMacro/DisjFalseMacro（level=1）核心证明：
  disj_force: A ∨ B ⟶ ¬B ⟶ A（用 force_disj_true1 + de Morgan + double_neg）
  disj_false: 子句字面值替换（eq_true/eq_false）+ disj_false_right 化简
  ↓
逆编码（关键）：encode_pt 的 CNF 约束逐条剥除——implies_elim + forall_intr/
forall_elim 清除 Tseitin 新变量（eqs 排序由索引正序反向清理）
  ↓
⊢ ¬t（应用 negI + double_neg）
```

**要点**：Tseitin 编码乘法本身携带证明（`encode_pt`），重建末期把 CNF 证明转换回
原命题的精确操作是 `implies_elim` 逐条剥假设 + `forall_intr/forall_elim` 清理新变量。

## 3. 对 Z3 重建（proofrec.py）的复用映射

| Z3 规则（proofrec 缺口） | 可复用来源（已删代码里的设计/名称） |
|---|---|
| `th-lemma`（real/int） | `verit_la_generic` 宏 + `verit_norm_lia/lra`、`verit_round_lia`；`int_*`/`real_*` 定理库（如 `int_geq_shift`、`int_add_comm`、`real_add_comm` 等） |
| `def-axiom`/`apply-def`/`intro-def`（Tseitin 变量引入） | zChaff：`tseitin.encode` 的等价证明 + 逆编码清理（剥假设 + 变量消除） |
| `quant-inst`/`quant-intro` | `verit_forall_inst`、`verit_sko_ex/for_sko_forall`、`verit_onepoint` |
| `nate/rewrite` 黑盒 | 无直接解（veriT 也是靠规则名）；候选 `hint_rewrite` 属性定理链反推 |
| prop/CNF 化简（`nnf-pos` 等） | `verit_conv`：`deMorgan_*`、`cnf_conv`、`imp_false_conv` 等 |

**架构结论**：veriT 证明格式明确 step=规则名+参数，所以重建可以「一宏一规则」
直接机械翻译；Z3 的 `rewrite` 步是黑盒（内含几十条内建规则，不逐个列出），
逐规则重建不可行。务实路线：**能把命名规则的步重建，`rewrite` 步用 eval
（或直接 oracle）信任**，即「可重建处重建、黑盒处信任」。

## 4. 已适配的关键库定理（重建可用）

（完整清单见 `theorem_map.tsv`，此处列两链路依赖骨架）

- 逻辑化简：`de_morgan_thm2`（`~(A|B) ⟷ ~A & ~B`）、`imp_trans`、`eq_true`/`eq_false`（替换定理）
- 消解/蕴含：`bdisj_or_intro`、`disj_left`、`disj_right`、`falseE`
- 线性算术（int/real）：`int_add_0_left`、`int_add_comm`、`int_geq`、`int_eq_move_left`、`int_geq_mul_pos/neg`、`int_geq_shift` 等；real 侧 `real_*` 对应定理
- 命题编码（sat 库）：`encode_conj`/`encode_disj`/`encode_imp`/`encode_eq`（Tseitin 编码的可证关系）

## 5. 已删除内容备注

2026-08 删除 `sat/`（zchaff+zeichenbar）与 `smt/veriT/`（约 8800 行 verit_macro +
conv + parser/proof_rec）。两包在主线（server/logic/domains/library）零引用，
其价值（重建设计、规则映射、待补齐位）已提取至本文件。库文件 `library/{sat,smt,verit}.pyhol`
保留（仍被 basic.load_library 处理）。