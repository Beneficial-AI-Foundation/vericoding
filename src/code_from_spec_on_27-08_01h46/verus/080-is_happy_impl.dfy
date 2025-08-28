use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
fn three_distinct(s: &Vec<char>, i: usize) -> (is: bool)
    requires
        0 < i && i + 1 < s.len(),
    ensures
        is <==> three_distinct_spec(s@, i as int),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1])
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if s.len() < 3 {
        return false;
    }
    
    let mut i: usize = 1;
    while i + 1 < s.len()
        invariant
            1 <= i < s.len(),
            s.len() >= 3,
            forall|j: int| 1 <= j < i ==> three_distinct_spec(s@, j),
        decreases s.len() - i,
    {
        if !three_distinct(s, i) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}