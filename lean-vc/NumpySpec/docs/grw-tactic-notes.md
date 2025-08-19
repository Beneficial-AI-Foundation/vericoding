# mathlib4 `grw` Tactic Documentation

## Overview
The `grw` tactic is a new addition to mathlib4 that allows rewriting with any relation, expanding beyond the typical `rw` tactic which is limited to equalities.

## Key Features

### Syntax Examples
```lean
example (h₁ : a ≤ b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example : (h₁ : a | b) (h₂ : b | c) : p | b * d := by
  grw [← h₁]
  exact h₂
```

### Design Philosophy
- Designed to have the same syntax and features as `rw`
- Cannot rewrite bound variables (same limitation as `rw`)
- Particularly useful for relations like:
  - Inequalities (≤, <)
  - Modular congruences ([ZMOD n])
  - Divisibility (|)
  - Custom relations

## Implementation Notes
- Initial implementation completed over 2 years ago
- Recently merged into mathlib4 after in-person review at Floris van Doorn's event
- Some lemmas tagged with `@[gcongr]` may need new use cases identified

## Community Reception
- Positive feedback from users like Terence Tao who see it as a natural enhancement
- Recognized as solving the long-standing limitation of rewriting with non-equality relations
- Expected to streamline many proofs involving order relations and congruences

## Future Considerations
- Additional lemmas may need tagging as use cases emerge
- Documentation improvements for edge cases
- Integration with other tactics in the mathlib4 ecosystem

## References
- Announcement by Jovan Gerbscheid on mathlib4 Discord
- PR merged after review at Floris van Doorn's session