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

/* helper modified by LLM (iteration 5): Fixed integer type annotations to avoid ghost code errors */
proof fn lemma_parentheses_depth_nonnegative(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        inner_depths_nonnegative(s)
    ensures
        parentheses_depth(s, i, j) >= 0
    decreases j - i
{
    if i == j {
        assert(parentheses_depth(s, i, j) == 0);
    } else {
        lemma_parentheses_depth_nonnegative(s, i + 1, j);
        if s[i] == '(' {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j) + 1);
        } else if s[i] == ')' {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j) - 1);
            assert(parentheses_depth(s, 0, i + 1) >= 0);
            assert(parentheses_depth(s, 0, i + 1) == parentheses_depth(s, 0, i) + (if s[i] == '(' {1} else if s[i] == ')' {-1} else {0}));
        } else {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j));
        }
    }
}

proof fn lemma_parentheses_depth_split(s: Seq<char>, i: int, j: int, k: int)
    requires
        0 <= i <= k <= j <= s.len()
    ensures
        parentheses_depth(s, i, j) == parentheses_depth(s, i, k) + parentheses_depth(s, k, j)
    decreases j - i
{
    if i == j {
        assert(parentheses_depth(s, i, j) == 0);
    } else if i == k {
        assert(parentheses_depth(s, i, k) == 0);
    } else {
        lemma_parentheses_depth_split(s, i + 1, j, k);
        if s[i] == '(' {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j) + 1);
            assert(parentheses_depth(s, i, k) == parentheses_depth(s, i + 1, k) + 1);
        } else if s[i] == ')' {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j) - 1);
            assert(parentheses_depth(s, i, k) == parentheses_depth(s, i + 1, k) - 1);
        } else {
            assert(parentheses_depth(s, i, j) == parentheses_depth(s, i + 1, j));
            assert(parentheses_depth(s, i, k) == parentheses_depth(s, i + 1, k));
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
    /* code modified by LLM (iteration 5): Fixed integer literal type annotations and ghost code usage */
    let mut groups = Vec::new();
    let mut current_start: usize = 0;
    let mut current_depth: int = 0;
    let mut i: usize = 0;
    
    while i < paren_string.len()
        invariant
            i <= paren_string.len(),
            current_start <= i,
            current_depth == parentheses_depth(paren_string@, current_start as int, i as int),
            forall|k: int| 0 <= k < groups.len() ==> parentheses_depth(groups[k as int]@, 0, groups[k as int].len() as int) == 0,
            forall|k: int| 0 <= k < groups.len() ==> inner_depths_positive(groups[k as int]@),
            groups.len() >= 0
        decreases paren_string.len() - i
    {
        let c = paren_string[i];
        if c == '(' {
            current_depth = current_depth + 1;
        } else if c == ')' {
            current_depth = current_depth - 1;
        }
        
        if current_depth == 0 {
            let mut group = Vec::new();
            let mut idx: usize = current_start;
            while idx <= i
                invariant
                    idx <= i + 1,
                    group@.len() == (idx - current_start) as int,
                    group@ =~= paren_string@.subrange(current_start as int, idx as int)
                decreases i - idx
            {
                if idx <= i {
                    group.push(paren_string[idx]);
                    idx = idx + 1;
                }
            }
            proof {
                lemma_parentheses_depth_split(paren_string@, 0, paren_string.len() as int, current_start as int);
                lemma_parentheses_depth_split(paren_string@, 0, paren_string.len() as int, (i + 1) as int);
                lemma_parentheses_depth_nonnegative(paren_string@, current_start as int, (i + 1) as int);
            }
            groups.push(group);
            current_start = i + 1;
        }
        
        i = i + 1;
    }
    
    groups
}
// </vc-code>


}

fn main() {}