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
proof fn lemma_depth_additive(s: Seq<char>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len()
    ensures
        parentheses_depth(s, i, k) == parentheses_depth(s, i, j) + parentheses_depth(s, j, k)
    decreases k - i
{
    if i == k {
    } else if i == j {
    } else if s[i] == '(' {
        lemma_depth_additive(s, i + 1, j, k);
    } else if s[i] == ')' {
        lemma_depth_additive(s, i + 1, j, k);
    } else {
        lemma_depth_additive(s, i + 1, j, k);
    }
}

proof fn lemma_depth_prefix_positive(s: Seq<char>, i: int, j: int)
    requires
        0 <= i < j <= s.len(),
        inner_depths_positive(s.subrange(i, j))
    ensures
        parentheses_depth(s, i, j) > 0
{
    assert(s.subrange(i, j)[0] == s[i]);
    assert(parentheses_depth(s.subrange(i, j), 0, 1) > 0);
    if s[i] == '(' {
        assert(parentheses_depth(s, i, i + 1) == 1);
    } else if s[i] == ')' {
        assert(parentheses_depth(s, i, i + 1) == -1);
        assert(false);
    } else {
        assert(parentheses_depth(s, i, i + 1) == 0);
        assert(false);
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
    /* code modified by LLM (iteration 5): fixed int type usage - moved depth computation into proof block */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    let mut start: usize = 0;
    
    while i < paren_string.len()
        invariant
            0 <= i <= paren_string.len(),
            0 <= start <= i,
            start < i ==> parentheses_depth(paren_string@, start as int, i as int) > 0,
            start == i ==> parentheses_depth(paren_string@, 0, i as int) == 0,
            forall|k: int| 0 <= k < result.len() ==> parentheses_depth(#[trigger] result[k]@, 0, result[k].len() as int) == 0,
            forall|k: int| 0 <= k < result.len() ==> inner_depths_positive(#[trigger] result[k]@)
    {
        if paren_string[i] == '(' {
            if start == i {
                start = i;
            }
            i = i + 1;
        } else if paren_string[i] == ')' {
            i = i + 1;
            if start < i {
                proof {
                    let depth = parentheses_depth(paren_string@, start as int, i as int);
                    if depth == 0 {
                        let mut group: Vec<char> = Vec::new();
                        let mut j: usize = start;
                        while j < i
                            invariant
                                start <= j <= i,
                                group.len() == j - start,
                                forall|k: int| 0 <= k < group.len() ==> group[k] == paren_string[(start + k) as int]
                        {
                            group.push(paren_string[j]);
                            j = j + 1;
                        }
                        
                        lemma_depth_additive(paren_string@, start as int, i as int - 1, i as int);
                        assert(group@ == paren_string@.subrange(start as int, i as int));
                        assert(forall|k: int| 0 < k < group.len() ==> parentheses_depth(group@, 0, k) == parentheses_depth(paren_string@, start as int, start as int + k));
                        assert forall|k: int| 0 < k < group.len() implies parentheses_depth(group@, 0, k) > 0 by {
                            if k < group.len() - 1 {
                                assert(start < start + k && start + k < i);
                                lemma_depth_additive(paren_string@, 0, start as int, start as int + k);
                                lemma_depth_additive(paren_string@, start as int, start as int + k, i as int);
                            } else {
                                assert(k == group.len() - 1);
                                lemma_depth_additive(paren_string@, start as int, i as int - 1, i as int);
                                lemma_depth_prefix_positive(paren_string@, start as int, i as int - 1);
                            }
                        }
                        
                        result.push(group);
                        start = i;
                    }
                }
            }
        } else {
            i = i + 1;
        }
    }
    result
}
// </vc-code>


}

fn main() {}