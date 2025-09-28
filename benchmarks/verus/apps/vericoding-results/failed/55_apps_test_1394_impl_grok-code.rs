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
spec fn remove_as_prefix(s: Seq<char>, k: int) -> Seq<char>
    requires
        0 <= k,
        k <= s.len() as int,
    decreases k
{
    if k == 0 {
        seq![]
    } else {
        let pref = s.subrange(0, k);
        if pref[0] != 'a' {
            seq![pref[0]].add(remove_as_prefix(s, k - 1))
        } else {
            remove_as_prefix(s, k - 1)
        }
    }
}

/* helper modified by LLM (iteration 4): add proof assertions to verify correctness */
proof fn lemma_remove_as_prefix_correct(s: Seq<char>, k: int)
    requires
        0 <= k,
        k <= s.len(),
    ensures
        remove_as_prefix(s, k) == remove_as(s.subrange(0, k)),
    decreases k
{
    if k > 0 {
        lemma_remove_as_prefix_correct(s, k - 1);
        let pref = s.subrange(0, k);
        if pref[0] != 'a' {
            assert(remove_as_prefix(s, k) == seq![pref[0]].add(remove_as_prefix(s, k - 1)));
            assert(remove_as(pref) == seq![pref[0]].add(remove_as(pref.subrange(1, pref.len() as int))));
        } else {
            assert(remove_as_prefix(s, k) == remove_as_prefix(s, k - 1));
            assert(remove_as(pref) == remove_as(pref.subrange(1, pref.len() as int)));
        }
    }
}

pub exec fn remove_as_exec(s: Vec<char>) -> (r: Vec<char>)
    ensures
        r@ == remove_as(s@)
{
    proof { lemma_remove_as_prefix_correct(s@, s@.len() as int); }
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@ == remove_as_prefix(s@, i as int),
        decreases s.len() - i
    {
        if s[i] != 'a' {
            result.push(s[i]);
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires t@.len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): ensure proper function call and return */
    let result = remove_as_exec(t);
    result
}
// </vc-code>


}

fn main() {}