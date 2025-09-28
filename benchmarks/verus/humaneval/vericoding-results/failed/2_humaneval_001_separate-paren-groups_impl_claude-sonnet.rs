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
/* helper modified by LLM (iteration 5): fixed integer literal type by adding int suffix */
proof fn lemma_depth_properties(s: Seq<char>, i: int, j: int, k: int)
    requires
        0 <= i <= k <= j <= s.len(),
    ensures
        parentheses_depth(s, i, j) == parentheses_depth(s, i, k) + parentheses_depth(s, k, j),
    decreases j - i
{
    if i == k {
        assert(parentheses_depth(s, i, k) == 0);
    } else if i < k {
        if s[i as int] == '(' {
            lemma_depth_properties(s, i + 1, j, k);
        } else if s[i as int] == ')' {
            lemma_depth_properties(s, i + 1, j, k);
        } else {
            lemma_depth_properties(s, i + 1, j, k);
        }
    }
}

proof fn lemma_depth_monotonic(s: Seq<char>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        parentheses_depth(s, i, k) == parentheses_depth(s, i, j) + parentheses_depth(s, j, k),
    decreases j - i
{
    lemma_depth_properties(s, i, k, j);
}
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
{
    /* code modified by LLM (iteration 5): fixed integer literal type by adding int suffix */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    let mut start = 0;
    
    while i < paren_string.len()
        invariant
            0 <= i <= paren_string.len(),
            0 <= start <= i,
            forall|k: int| 0 <= k < result.len() ==> parentheses_depth(#[trigger] result[k as int]@, 0, result[k as int].len() as int) == 0,
            forall|k: int| 0 <= k < result.len() ==> inner_depths_positive(#[trigger] result[k as int]@),
            parentheses_depth(paren_string@, start as int, i as int) >= 0,
    {
        if paren_string[i] == ')' {
            let ghost start_int: int = start as int;
            let ghost i_plus_1_int: int = (i + 1) as int;
            if parentheses_depth(paren_string@, start_int, i_plus_1_int) == 0int {
                let mut group = Vec::new();
                let mut j = start;
                while j <= i
                    invariant
                        start <= j <= i + 1,
                        j - start == group.len(),
                        forall|k: int| 0 <= k < group.len() ==> group[k as int] == paren_string[(start + k) as int],
                {
                    group.push(paren_string[j]);
                    j += 1;
                }
                proof {
                    lemma_depth_properties(paren_string@, start_int, i_plus_1_int, start_int);
                    lemma_depth_monotonic(paren_string@, start_int, i_plus_1_int, paren_string.len() as int);
                }
                result.push(group);
                start = i + 1;
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}