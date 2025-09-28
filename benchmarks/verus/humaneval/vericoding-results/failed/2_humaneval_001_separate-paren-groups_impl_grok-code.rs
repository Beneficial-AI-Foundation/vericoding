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
/* helper modified by LLM (iteration 3): Fixed return type annotation to (result: int) to properly reference result in ensures clause */
fn exec_parentheses_depth(s: &Vec<char>, i: usize, j: usize) -> (result: int)
    requires
        0 <= i && i <= j && j <= s.len(),
        decreases j - i
    ensures
        result == parentheses_depth(s@, i as int, j as int)
{
    let mut depth = 0int;
    let mut k = i;
    while k < j
        invariant
            0 <= k <= j,
            depth == parentheses_depth(s@, i as int, k as int),
        decreases j - k
    {
        if s[k] == '(' {
            depth = depth + 1;
        } else if s[k] == ')' {
            depth = depth - 1;
        }
        // else no change
        k = k + 1;
    }
    proof {
        assert(depth == parentheses_depth(s@, i as int, j as int));
    }
    depth
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
    /* code modified by LLM (iteration 5): removed parentheses from decreases clause */
    let mut groups: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    let mut depth = 0int;
    let mut idx: usize = 0;
    while idx < paren_string.len()
        invariant
            depth == parentheses_depth(paren_string@, 0, idx as int),
            forall |k: int| 0 <= k < groups@.len() ==> (
                parentheses_depth(groups@[k]@, 0, groups@[k]@.len() as int) == 0,
                inner_depths_positive(groups@[k]@)
            ),
            current@.len() as int <= paren_string@.len() as int - idx as int,
            depth >= 0,
        decreases paren_string@.len() as int - idx as int
    {
        let c = paren_string[idx];
        if c == '(' {
            depth = depth + 1;
            current.push(c);
        } else if c == ')' {
            depth = depth - 1;
            current.push(c);
            if depth == 0 {
                groups.push(current);
                current = Vec::new();
            }
        } else {
            current.push(c);
        }
        idx = idx + 1;
    }
    proof {
        assert(depth == 0);
        assert(forall |k: int| 0 <= k < groups@.len() ==> (
            parentheses_depth(groups@[k]@, 0, groups@[k]@.len() as int) == 0,
            inner_depths_positive(groups@[k]@)
        ));
    }
    groups
}
// </vc-code>


}

fn main() {}