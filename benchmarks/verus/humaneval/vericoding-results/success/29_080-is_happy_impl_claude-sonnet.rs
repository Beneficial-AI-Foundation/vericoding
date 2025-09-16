// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type safety with nat for index bounds */
fn check_three_distinct(s: &Vec<char>, i: usize) -> (ret: bool)
    requires
        0 < i < s.len(),
        i + 1 < s.len(),
    ensures
        ret <==> three_distinct_spec(s@, i as int),
{
    s[i - 1] != s[i] && s[i] != s[i + 1]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)

    ensures
        happy <==> happy_spec(s@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix arithmetic overflow and precondition issues */
    if s.len() < 3 {
        return false;
    }
    
    let mut idx: usize = 1;
    while idx < s.len() - 1
        invariant
            1 <= idx <= s.len() - 1,
            s.len() >= 3,
            forall|i: int| 0 < i < idx && i + 1 < s.len() ==> three_distinct_spec(s@, i),
        decreases s.len() - 1 - idx
    {
        if !check_three_distinct(s, idx) {
            return false;
        }
        idx = idx + 1;
    }
    true
}
// </vc-code>

}
fn main() {}