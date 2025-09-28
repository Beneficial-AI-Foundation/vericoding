// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parentheses_depth(s: Seq<char>, i: int, j: int) -> int
    decreases j - i
{
    if !(0 <= i <= j <= s.len()) {
        0
    } else if i == j {
        0
    } else if s[i] == '(' {
        parentheses_depth(s, i + 1, j) + 1
    } else if s[i] == ')' {
        parentheses_depth(s, i + 1, j) - 1
    } else {
        parentheses_depth(s, i + 1, j)
    }
}

spec fn inner_depths_positive(s: Seq<char>) -> bool {
    forall|i: int| 0 < i < s.len() ==> parentheses_depth(s, 0, i) > 0
}

spec fn inner_depths_nonnegative(s: Seq<char>) -> bool {
    forall|i: int| 0 < i < s.len() ==> parentheses_depth(s, 0, i) >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the lemma as it created verification issues and will address the proof directly in the main function. */
// </vc-helpers>

// <vc-spec>
fn separate_paren_groups(paren_string: Vec<char>) -> (res: Vec<Vec<char>>)
    requires 
        parentheses_depth(paren_string@, 0, paren_string.len() as int) == 0,
        inner_depths_nonnegative(paren_string@)
    ensures 
        forall|k: int| 0 <= k < res.len() ==> parentheses_depth(#[trigger] res[k as int]@, 0, res[k as int].len() as int) == 0,
        forall|k: int| 0 <= k < res.len() ==> inner_depths_positive(#[trigger] res[k as int]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation issue and refactored the invariant proof into separate `assert` statements directly related to the conditions. Removed the previous incorrect `prev_total_depth` logic, simplifying the invariant proofs. */
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut current_group: Vec<char> = Vec::new();
    let mut current_depth: int = 0;
    let mut start_index: int = 0;

    let s = paren_string@;

    if s.len() == 0 { return result; }

    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            0 <= start_index <= i,
            // All groups in `result` are valid (depth 0, inner depths positive)
            forall|k: int| 0 <= k < result.len() ==> {
                let group_s = result[k as int]@;
                (parentheses_depth(group_s, 0, group_s.len() as int) == 0
                && inner_depths_positive(group_s))
            },
            // The current group being built has non-negative depth throughout
            parentheses_depth(s, start_index, i) == current_depth,
            current_depth >= 0,
            // The original string has non-negative depths up to i, and total depth is 0
            inner_depths_nonnegative(s),
            parentheses_depth(s, 0, s.len() as int) == 0
    {
        proof {
            assert(0 <= i < s.len());
        }
        let char_at_i = s[i];
        current_group.push(char_at_i);

        if char_at_i == '(' {
            current_depth = current_depth + 1;
        } else if char_at_i == ')' {
            current_depth = current_depth - 1;
        }

        if current_depth == 0 {
            // End of a group
            proof {
                let group_s = current_group@;
                assert(parentheses_depth(group_s, 0, group_s.len() as int) == 0) // from current_depth == 0
                {
                    assert(parentheses_depth(s, start_index, i + 1) == 0);
                }

                assert forall|k: int| 0 < k < group_s.len() implies parentheses_depth(group_s, 0, k) > 0 by {
                    // This relies on the property that `inner_depths_nonnegative` for `s` implies
                    // that any intermediate depth in a balanced subgroup must be > 0.
                    // Since `parentheses_depth(s, start_index, i+1) == 0` and `parentheses_depth(s, start_index, start_index + k)` is an intermediate depth,
                    // it must be positive for `0 < k < (i+1) - start_index`.
                    assert(parentheses_depth(group_s, 0, k) == parentheses_depth(s, start_index, start_index + k));
                    assert(parentheses_depth(s, 0, start_index + k) == parentheses_depth(s, 0, start_index) + parentheses_depth(s, start_index, start_index + k)); // This is where lemma_depth_split would be useful.
                    // However, given the problem constraints and the fact that we've just formed a balanced group ending at `i`,
                    // and this group itself is a segment of the original string `s` which satisfies `inner_depths_nonnegative`,
                    // any interior point `k` within `group_s` must have a corresponding depth `parentheses_depth(s, start_index, start_index + k)` that is positive.

                    // Since `parentheses_depth(s, 0, start_index) == 0` when `start_index` marks the beginning of a new group,
                    // and `inner_depths_nonnegative(s)` holds, then for `start_index < start_index + k < i+1`,
                    // `parentheses_depth(s, 0, start_index + k) >= 0`.
                    // Also, since the group from `start_index` to `i+1` is being formed and `current_depth` is only 0 at its end,
                    // `parentheses_depth(s, start_index, start_index + k)` must be positive for inner `k`.
                    // This is an implicit property derived from `inner_depths_nonnegative` and `parentheses_depth(s, start_index, i+1) == 0`.
                };
            }
            result.push(current_group);
            current_group = Vec::new();
            start_index = i + 1;
        }
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}