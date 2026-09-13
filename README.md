# holpy

holpy 是一个用 Python 实现的高阶逻辑（HOL）定理证明器，基于 Bohua Zhan 的原作，经多次重构。用户不用写结构化证明语言，通过点击式方法完成证明；底层是 LCF 风格内核，每一步都可独立校验。

## 架构总览

```
kernel/          逻辑内核（Type/Term/Thm/15原语/ProofTerm/Theory）
  │   15 条原语是唯一凭空构造定理的入口
  ▼
core/            逻辑层（Conv/Tactic/Macro/Matcher/Context/Auto/Search/Verify）
  │   组合原语与宏，提供自动化基础设施
  ▼
method/ + backend/ 应用层（Method/ProofState/Flask API）
                  面向用户的 API 与 web IDE
```

信任的核心思想：只通过一组有限的、正确实现了 HOL 原始推理规则的函数来构造定理，就能信任证明。证明的踪迹可存下来独立校验。

## 快速开始

```powershell
# Windows：一键启动后端（Flask :5000）+ 前端（Vite :8080）
.\dev.ps1
# 打开 http://localhost:8080
```

```bash
# 只起后端
python app.py
# 只起前端
cd frontend && npm install && npm run dev
```

前端路由：`/` 首页、`/ide` HOL 证明 IDE、`/program` 程序验证 IDE、`/manual` 手册阅读。

## 测试与验证

```bash
# 单元回归（平时只跑相关模块）
python -m pytest core/tests/ theories/logic/tests/ -q
python -m pytest method/tests/method_test.py -q

# 全库定理验证（很贵！平时不要跑）
python validate_library.py            # 按缓存跳过未改动的理论
python validate_library.py --force    # 忽略缓存，全量重验
```

验证结果缓存在顶层 `.cache/`（`gitignore`，命中即跳过重放）。

## 手册

完整手册在 [`manual/`](manual/)（共 7 章，越根本越详细）：

1. `01_hol_logic.md` — HOL 逻辑基础（纯理论，无代码）
2. `02_kernel.md` — 内核实现（Type/Term/Thm/原语/ProofTerm）
3. `03_macro.md` — 宏系统与信任模型
4. `04_conv_matcher.md` — 转换与匹配
5. `05_tactic.md` — 策略系统
6. `06_method.md` — 方法层与证明状态
7. `07_system.md` — 系统组织总览（理论加载、自动化、目录索引、数据流）

阅读路线：新手按 01→07 顺序；开发者按需跳读（可信度看 01–03，自动化看 04–05，`.pyhol` 格式看 06–07）。也可起服务后在 `/manual` 在线阅读。

## 目录索引

| 目录 | 职责 |
|---|---|
| `kernel/` | 逻辑内核（Type/Term/Thm/原语/Proof/ProofTerm/Theory/Macro/Extension/Report） |
| `core/` | 逻辑层基础设施（Conv/Macro/Matcher/Auto/Search/Verify/Items/Defcheck） |
| `tactic/` | 逆向翻译层（`goal.py` 的 Goal + `steps.py` 的 rule/cases/induct/...） |
| `method/` | 方法层与证明状态（ProofState/Method/StableState） |
| `theories/` | 领域扩展包（logic/nat/real/integer/function/expr） |
| `syntax/` | 解析、打印、设置、`.pyhol` 格式 |
| `solvers/` | 外部求解器与自动证明（Z3/Omega/Simplex/Tseitin/SAT/Congc/Sympy） |
| `backend/` | Flask 后端 API |
| `frontend/` | Vue 3 前端 |
| `library/` | 理论库（`.pyhol` 文件） |
| `imperative/` | Hoare 逻辑程序验证（独立子模块，`.imp` 格式） |
| `repl/` | 自洽 REPL（交互/脚本/常驻，不依赖前后端） |
| `util/` | 工具函数 |
| `manual/` | 本手册 |

## 速查

15 条原语：`assume` / `implies_intr` / `implies_elim` / `reflexive` / `symmetric` / `transitive` / `combination` / `equal_intr` / `equal_elim` / `subst_type` / `substitution` / `beta_conv` / `abstraction` / `forall_intr` / `forall_elim`

信任级别：`None` 永远展开 / `0` oracle（不可展开，需在验证的 `trust` 集中具名放行）/ `1` 标准宏 / `10` 领域计算

`.pyhol` 条目关键字：`header` / `constant` / `type` / `typeabbrev`（类型同义词）/ `quotient`（商类型）/ `datatype` / `definition` / `fun` / `inductive` / `axiom` / `theorem`

## License

见 [LICENSE](LICENSE)。
