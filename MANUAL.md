# HOLPy Proof Manual

## Architecture

```
Layer 3: Methods (user-facing, server/methods/)
  apply_backward_step, introduction, rewrite_goal, ...
  |
Layer 2: Tactics + Conversions (logic/)
  rule, intros, assumption, reflexive, equal_intr, ...
  rewr_conv, top_conv, beta_norm_conv, ...
  |
Layer 1: Macros (logic/macros/)
  apply_theorem, rewrite_goal, trivial, ...
  |
Layer 0: Primitives (kernel/thm.py)
  assume, implies_intr, implies_elim, reflexive, symmetric,
  transitive, combination, equal_intr, equal_elim,
  substitution, subst_type, beta_conv, abstraction,
  forall_intr, forall_elim
```

## Layer 0: Primitives

15 primitive rules. Everything must reduce to these.

| Rule | Signature | Description |
|------|-----------|-------------|
| `assume(A)` | `A \|- A` | Assumption |
| `implies_intr(A, th)` | `A \|- B` → `\|- A --> B` | Implication introduction |
| `implies_elim(th1, th2)` | `\|- A-->B, \|- A` → `\|- B` | Modus ponens |
| `reflexive(x)` | `\|- x = x` | Reflexivity |
| `symmetric(th)` | `\|- x=y` → `\|- y=x` | Symmetry |
| `transitive(th1, th2)` | `\|- x=y, \|- y=z` → `\|- x=z` | Transitivity |
| `combination(th1, th2)` | `\|- f=g, \|- x=y` → `\|- f x = g y` | Congruence |
| `equal_intr(th1, th2)` | `\|- A-->B, \|- B-->A` → `\|- A=B` | Iff introduction |
| `equal_elim(th1, th2)` | `\|- A=B, \|- A` → `\|- B` | Iff elimination |
| `substitution(inst, th)` | Term substitution | |
| `subst_type(tyinst, th)` | Type substitution | |
| `beta_conv(t)` | `\|- (%x. t1) t2 = t1[t2/x]` | Beta conversion |
| `abstraction(x, th)` | `\|- t1=t2` → `\|- (%x.t1) = (%x.t2)` | Abstraction |
| `forall_intr(x, th)` | `\|- t` → `\|- !x. t` | Universal introduction |
| `forall_elim(s, th)` | `\|- !x. t` → `\|- t[s/x]` | Universal elimination |

## Layer 1: Macros

Derived proof methods. Each has `eval()` (fast) and `get_proof_term()` (detailed).

| Macro | Description |
|-------|-------------|
| `apply_theorem` | Apply a theorem with matching and substitution |
| `apply_fact` | Apply a forall/implies fact to other facts |
| `rewrite_goal` | Rewrite goal using an equality theorem |
| `rewrite_goal_with_prev` | Rewrite goal using a previous equality fact |
| `rewrite_fact` | Rewrite a fact using an equality theorem |
| `trivial` | Prove `A1 --> ... --> An --> C` when `C` is among `Ai` |
| `intros` | Introduce variables and assumptions |
| `resolution` | Propositional resolution |
| `beta_norm` | Beta-normalize a theorem |

## Layer 2: Tactics

Tactics transform goals into subgoals. A tactic takes a goal (Thm) and returns a ProofTerm that may contain `sorry` gaps.

### Atomic Tactics

| Tactic | Goal → Subgoals | Description |
|--------|-----------------|-------------|
| `rule(th_name)` | `?- G` → `?- A1, ..., ?- An` | Apply theorem backward. Matches conclusion. |
| `assumption` | `A |- A` → (none) | Solve if goal is in hypotheses. |
| `reflexive` | `?- t = t` → (none) | Solve by reflexivity. |
| `equal_intr` | `?- A = B` → `?- A-->B, ?- B-->A` | Split equality into two implications. |
| `intros` | `?- !x. A-->B` → `x, A |- B` | Strip forall and implications. |
| `var_induct` | `?- P x` → induction cases | Apply induction principle. |
| `rewrite_goal(th)` | `?- G` → `?- G'` | Rewrite goal using theorem. |
| `rewrite_goal_with_prev` | `?- G` → `?- G'` | Rewrite using previous fact. |
| `apply_prev` | `?- C` → (none or subgoals) | Apply previous fact to goal. |
| `cases(A)` | `?- C` → `A-->C, ~A-->C` | Case analysis. |

### Combinators

| Combinator | Description |
|------------|-------------|
| `then_tac(t1, t2)` | Apply t1, then t2 to all subgoals |
| `else_tac(t1, t2)` | Try t1, fallback to t2 |
| `repeat_tac(t)` | Apply t repeatedly until failure |
| `try_tac(t)` | Apply t, succeed even if t fails |
| `thenl_tac(t, [t1, t2, ...])` | Apply t, then ti to i-th subgoal |

### Conversion Tactics

| Tactic | Description |
|--------|-------------|
| `rewr_conv(th)` | Rewrite using equality theorem `|- lhs = rhs` |
| `top_conv(cv)` | Apply cv everywhere (top-down) |
| `top_sweep_conv(cv)` | Top-down sweep, stop on first success |
| `bottom_conv(cv)` | Bottom-up traversal |
| `then_conv(cv1, cv2)` | Sequential composition |
| `else_conv(cv1, cv2)` | Fallback |
| `arg_conv(cv)` | Apply to argument of application |
| `fun_conv(cv)` | Apply to function of application |
| `beta_norm_conv()` | Full beta normalization |

## Layer 3: Methods

Methods are the user-facing API. Each method has:
- `search(state, id, prevs)` → suggestions
- `apply(state, id, data, prevs)` → modify proof state

### Core Methods

| Method | Args | Description |
|--------|------|-------------|
| `apply_backward_step` | theorem, [fact_ids] | Apply theorem backward to goal |
| `apply_forward_step` | theorem, [fact_ids] | Apply theorem forward to derive fact |
| `apply_prev` | [fact_ids] | Apply previous fact to goal |
| `introduction` | [names] | Introduce variables and assumptions |
| `rewrite_goal` | theorem, [sym] | Rewrite goal using theorem |
| `rewrite_goal_with_prev` | [fact_ids] | Rewrite goal using previous fact |
| `rewrite_fact` | theorem, [fact_ids] | Rewrite a fact |
| `rewrite_fact_with_prev` | [fact_ids] | Rewrite fact using another fact |
| `induction` | theorem, var | Apply induction |
| `cases` | term | Case analysis |
| `reflexive` | — | Prove t = t |
| `equal_intr` | — | Prove A = B from A-->B and B-->A |
| `insert` | theorem | Insert theorem as new line |
| `forall_elim` | term | Instantiate forall |
| `inst_exists_goal` | term | Instantiate existential goal |
| `simp` | — | Simplify using hint_rewrite theorems |
| `norm` | — | Normalize (nat/real) |
| `eval` | — | Evaluate (nat/real) |
| `z3` | — | Invoke Z3 solver |

## Proof Patterns

### Pattern 1: Iff Split

Goal: `?- A <--> B`

```
0: apply_backward_step iffI
0: introduction
0.1: ... prove A --> B ...
1: introduction
1.1: ... prove B --> A ...
```

### Pattern 2: Conjunction

Goal: `?- A & B`

```
0: apply_backward_step conjI
0: introduction
0.1: ... prove A ...
0.2: ... prove B ...
```

### Pattern 3: Disjunction

Goal: `?- A | B`

```
0: apply_backward_step disjI1
0: ... prove A ...
```

Or case analysis:

```
0: apply_backward_step disjE @fact
0: introduction
0.1: ... prove from A ...
1: introduction
1.1: ... prove from B ...
```

### Pattern 4: Negation

Goal: `?- ~A`

```
0: apply_backward_step negI
0: introduction
0.1: ... prove false from A ...
```

### Pattern 5: Contradiction

Goal: `?- false` (with ~A and A in hyps)

```
0: apply_backward_step negE @hyp_not_A, hyp_A
```

### Pattern 6: Explosion

Goal: `?- C` (with false in hyps)

```
0: apply_backward_step falseE @hyp_false
```

### Pattern 7: Reflexivity

Goal: `?- t = t`

```
0: reflexive
```

### Pattern 8: Symmetry

Goal: `?- a = b` (with b = a as fact)

```
0: apply_backward_step eq_sym_eq
```

### Pattern 9: Rewrite Chain

Goal: `?- C` (where C can be simplified)

```
0: rewrite_goal th1
0: rewrite_goal th2
0: rewrite_goal_with_prev @fact
```

### Pattern 10: Classical Reasoning

Goal: `?- C` (need excluded middle)

```
0: apply_backward_step classical_cases
0: introduction
0.1: ... prove from A ...
1: introduction
1.1: ... prove from ~A ...
```

## Design Principles

1. **Atomic tactics do one thing**: `rule` matches and applies, `assumption` checks hyps, `reflexive` proves equality.

2. **Combinators compose**: `then_tac(then_tac(a, b), c)` = `then_tac(a, then_tac(b, c))`.

3. **Methods hide complexity**: `apply_backward_step` internally calls `rule`, handles matching, creates subgoals.

4. **Conversions are reusable**: The same `rewr_conv` works in `rewrite_goal`, `rewrite_fact`, `simp`.

5. **Macros bridge layers**: `apply_theorem` macro is used by both `apply_backward_step` method and `rule` tactic.
