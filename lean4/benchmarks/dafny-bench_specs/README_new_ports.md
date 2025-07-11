# Newly Ported Dafny Specifications

This document lists the 10 Dafny specifications that were newly ported to Lean 4 on 2025-07-09.

## Ported Specifications

1. **LongestPrefix.lean** - Find the longest common prefix of two character sequences
   - Original: Clover_longest_prefix_spec.dfy
   - Function: `longestCommonPrefix`

2. **Match.lean** - Check if a string matches a pattern with '?' wildcards
   - Original: Clover_match_spec.dfy
   - Function: `matchPattern`

3. **MaxArray.lean** - Find the maximum element in a non-empty array
   - Original: Clover_max_array_spec.dfy
   - Function: `maxArray`

4. **MinArray.lean** - Find the minimum element in a non-empty array
   - Original: Clover_min_array_spec.dfy
   - Function: `minArray`

5. **MinOfTwo.lean** - Find the minimum of two integers
   - Original: Clover_min_of_two_spec.dfy
   - Function: `minOfTwo`

6. **Modify2DArray.lean** - Modify a single element in a 2D array
   - Original: Clover_modify_2d_array_spec.dfy
   - Function: `modifyArrayElement`

7. **MultiReturn.lean** - Compute sum and difference of two integers
   - Original: Clover_multi_return_spec.dfy
   - Function: `multipleReturns`

8. **OnlineMax.lean** - Find position of first element after index x that exceeds max of elements before x
   - Original: Clover_online_max_spec.dfy
   - Function: `onlineMax`

9. **OnlyOnce.lean** - Check if an element appears exactly once in an array
   - Original: Clover_only_once_spec.dfy
   - Function: `onlyOnce`

10. **Quotient.lean** - Integer division with remainder
    - Original: Clover_quotient_spec.dfy
    - Function: `quotient`

## Implementation Notes

- All specifications use Hoare triple syntax: `⦃⌜precondition⌝⦄ program ⦃⇓result => ⌜postcondition⌝⦄`
- Proofs are left as `sorry` for future implementation
- Functional style is used throughout (no mutable state except where necessary)
- Array indexing uses safe access patterns with proof obligations where needed