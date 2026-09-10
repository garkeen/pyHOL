# tactic/ - L2 逆向翻译层（ARCHITECTURE_AUDIT.md §2）。
#
# 全序：kernel < conv < macro < tactic < method。tactic 层是
# 逆向推理的翻译器：读 goal，把 goal 形状翻译成"宏名+参数"
# （+显式子目标），不含推导逻辑、无 THEN/ORELSE/REPEAT 组合子。
#
#   goal.py   Goal 概念的全系统唯一定义点（开洞语句的铸造处）
#   steps.py  Tactic 基类 + rule/cases/intro/induct/rewrite/...
#             各战术 = 形状分析 + 宏名+参数
#
# 消费方（method/、theories/<域>/tactic、imperative/）经
# `from tactic import steps as tactic` 取战术类；goal 经
# `from tactic.goal import Goal`。