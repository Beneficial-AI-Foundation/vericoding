// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn count_as(s: Seq<char>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else if s[0] == 'a' {
            1 + count_as(s.subrange(1, s.len() as int))
        } else {
            count_as(s.subrange(1, s.len() as int))
        }
    }
    
    spec fn remove_as(s: Seq<char>) -> Seq<char>
        decreases s.len()
    {
        if s.len() == 0 {
            seq![]
        } else if s[0] == 'a' {
            remove_as(s.subrange(1, s.len() as int))
        } else {
            seq![s[0]].add(remove_as(s.subrange(1, s.len() as int)))
        }
    }
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_as_nonneg(s: Seq<char>)
    ensures count_as(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_as_nonneg(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_remove_as_length(s: Seq<char>)
    ensures remove_as(s).len() == s.len() - count_as(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[0] == 'a' {
        lemma_remove_as_length(s.subrange(1, s.len() as int));
    } else {
        lemma_remove_as_length(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_count_as_bounded(s: Seq<char>)
    ensures count_as(s) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_as_bounded(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 5): fixed max call to use spec mode */
spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn lemma_remove_as_prefix(s: Seq<char>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures remove_as(s.subrange(0, j)).subrange(0, remove_as(s.subrange(0, i)).len() as int) == remove_as(s.subrange(0, i))
    decreases s.len()
{
    if i == 0 {
        return;
    }
    if j == 0 {
        return;
    }
    if s[0] == 'a' {
        lemma_remove_as_prefix(s.subrange(1, s.len() as int), max_int(i-1, 0), j-1);
    } else {
        lemma_remove_as_prefix(s.subrange(1, s.len() as int), max_int(i-1, 0), j-1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified proof approach */
    proof {
        lemma_count_as_nonneg(t@);
        lemma_count_as_bounded(t@);
        lemma_remove_as_length(t@);
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < t.len()
        invariant
            0 <= i <= t.len(),
            result@ == remove_as(t@.subrange(0, i as int)),
        decreases t.len() - i
    {
        if t[i] != 'a' {
            result.push(t[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}