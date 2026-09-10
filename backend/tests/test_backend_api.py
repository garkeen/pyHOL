"""
后端 API 测试归档（知识注释版）。

本文件原先是手写脚本 test_backend_api.py（旧位：仓库根目录），
通过 Flask test_client 逐个锤 /api/* 端点。它有两个严重病灶：

  1. pytest 模式下 12 error（缺 `client` fixture，函数签名直接失败），
     只有脚本模式（python test_backend_api.py）能跑；
  2. save round-trip 测试写回**真实 library/**（basic.user_dir()），
     不是临时副本 —— 跑一次就污染库文件（曾污染 logic_base.pyhol 已还原）。

用户拍板：真正的测试以后再写。因此本文件降级为**知识归档**——
保留原测试覆盖的 API 面、载荷形状、断言意图，供未来 pytest
重写参考；不构造 client 也不写任何库文件。

═══ 原测试覆盖的 12 个端点 ═══

1. POST /api/find-files
   入：{} → 出：{'theories': [...]}，断言非空。
   列全部理论文件（metadata）；被主 IDE 文件列表消费。

2. POST /api/load-json-file
   入：{'filename': <name>, 'line_length': 80}
   出：{'name', 'content': [条目{}]}；content 每项含 'ty'（如 'thm'/'def.ax'）。
   加载 .pyhol 并解析为 JSON 条目列表。

3. POST /api/save-file   ← 病灶 2 的入口
   入：{'filename': <name>, 'content': <load-json-file 的 content>}
   出：200 即成功。
   把整个条目列表写回磁盘 .pyhol（真实库目录！）。

4. POST /api/check-modify
   入：{'filename', 'line_length', 'item': {条目}}
   出：{'item': {检查后条目}}；'error' 键存在即检查失败。
   条目合法性检查（定义/定理），前端编辑保存前调用。

5. POST /api/check-modify 无 limit_ty/limit_name（新条目流程）
   同上，但 item 是待创建的新条目（无 limit 限定）。

6. POST /api/v2/init-saved-proof
   入：{'theory_name', 'thm_name', 'vars', 'prop', 'steps': []}
   出：{'state': {'proof': [...]}} 或 {'error': ...}。
   以稳定 ID 管线初始化一个证明会话（StableProofState）。

7. POST /api/find-link
   入：{'filename', 'ext_ty': 'thm.ax', 'name': 'conjI'}
   出：链接定位信息。
   查找条目所在位置（link 导航用）。

8. PUT  /api/remove-file
   入：{'filename': <name>} → 出 200。
   删除理论文件。

═══ 原测试各自断言意图（pytest 重写时可恢复）═══

- test_find_files: 理论列表非空。
- test_load_json_file: 字段 name/content 存在，content 为条目数组；
  统计 ty 分布（曾见 logic_base 有 'thm'/'def.ax' 等）。
- test_save_round_trip: 保存后磁盘 parse_pyhol 条目数 == 原数；
  再 load 也 == 原数（round-trip 一致性）。
- test_add_axiom_and_persist: 追加 'thm.ax' 条目 → 保存 → 磁盘条目数+1
  且新条目存在 → 重载数+1 → 清理后条目数还原。
- test_add_definition_and_persist: 追加 'def.ax' 条目，同理验证持久化+清理。
- test_create_new_theory_file: 写全新理论 '__test_new_theory__'
  （3 条目：header/def.ax/thm.ax）→ 保存 → 磁盘存在 → 解析验证 → 删除。
- test_check_modify: 'def.ax' 条目过 check-modify，断言返回 'item'。
- test_check_modify_no_limit: 无 limit 的新条目 check-modify，断言 200。
- test_new_theorem_prove_flow: check-modify → init-saved-proof 两步联动。
- test_init_saved_proof: 平凡命题（'A ⟶ A'）初始化证明状态。
- test_find_link: 已知公理 conjI 的 link 定位。
- test_remove_file: 造临时文件 → PUT remove-file → 断言文件不存在。

═══ 重写 checklist（避免旧病灶复发）═══

- [ ] 用 pytest fixture 提供 client（backend.app create_app().test_client()）；
- [ ] 沙箱：save/remove/create 一律指向临时目录，禁止 basic.user_dir();
- [ ] 删除本归档后，把上面的端点矩阵转成真正的 pytest 用例；
- [ ] 唯一必需端到端：load → save → reload 于同一临时库。

（原文：本文件由 git mv 自仓库根目录 test_backend_api.py，2026-09-09。）
"""
