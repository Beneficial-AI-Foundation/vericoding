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
/* helper modified by LLM (iteration 5): fixed requires block by combining conditions into a single block with commas */
proof fn lemma_substring_depth(s: Seq<char>, a: int, b: int, j: int)
    requires
        0 <= a <= b <= s.len(),
        0 <= j <= b - a,
    ensures
        parentheses_depth(s.subrange(a, b), 0, j) == parentheses_depth(s, a, a+j),
    decreases b - a - j
{
    if j == 0 {
        // both sides are 0
    } else {
        let s_sub = s.subrange(a, b);
        let first_char = s_sub[0];
        if first_char == '(' {
            assert(parentheses_depth(s_sub, 0, j) == 1 + parentheses_depth(s_sub, 1, j));
            lemma_substring_depth(s, a+1, b, j-1);
            assert(parentheses_depth(s_sub, 1, j) == parentheses_depth(s, a+1, a+1 + (j-1)));
            assert(parentheses_depth(s, a, a+j) == 1 + parentheses_depth(s, a+1, a+j));
        } else if first_char == ')' {
            assert(parentheses_depth(s_sub, 0, j) == -1 + parentheses_depth(s_sub, 1, j));
            lemma_substring_depth(s, a+1, b, j-1);
            assert(parentheses_depth(s_sub, 1, j) == parentheses_depth(s, a+1, a+1 + (j-1)));
            assert(parentheses_depth(s, a, a+j) == -1 + parentheses_depth(s, a+1, a+j));
        } else {
            assert(parentheses_depth(s_sub, 0, j) == parentheses_depth(s_sub, 1, j));
            lemma_substring_depth(s, a+1, b, j-1);
            assert(parentheses_depth(s_sub, 1, j) == parentheses_depth(s, a+1, a+1 + (j-1)));
            assert(parentheses_depth(s, a, a+j) == parentheses_depth(s, a+1, a+j));
        }
    }
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
    /* code modified by LLM (iteration 5): fixed indexing operation to use usize indices */
    let n = paren_string.len();
    let mut i = 0;
    let mut start = 0;
    let mut depth = 0;
    let mut res = Vec::new();

    while i < n
        invariant
            0 <= start <= i <= n,
            depth == parentheses_depth(paren_string@, start as int, i as int),
            forall|k: int| (start as int) + 1 <= k < (i as int) ==> parentheses_depth(paren_string@, start as int, k) > 0,
        decreases n - i
    {
        let c = paren_string[i];
        if c == '(' {
            depth += 1;
        } else if c == ')' {
            depth -= 1;
        }

        if depth == 0 && i > start {
            let group = paren_string[start..i+1].to_vec();
            res.push(group);
            start = i+1;
        }

        i += 1;
    }

    res
}
// </vc-code>


}

fn main() {}