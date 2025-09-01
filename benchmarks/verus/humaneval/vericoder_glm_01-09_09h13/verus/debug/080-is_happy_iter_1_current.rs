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
fn reveal_three_distinct_lemma(s: Seq<char>, i: int)
    requires 0 < i && i+1 < s.len()
    ensures three_distinct_spec(s, i) <==> (s[i-1] != s[i] && s[i] != s[i+1])
{
    reveal(three_distinct_spec);
    assert((s[i-1] != s[i] && s[i] != s[i+1]) == ((s[i-1] != s[i]) && (s[i] != s[i+1]) && (s[i] != s[i+1])));
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
    let mut i = 1;
    while i < s.len() - 1
        invariant
            1 <= i <= s.len() - 1,
            forall|j: int| 0 < j < i ==> three_distinct_spec(s@, j)
    {
        if s[i-1] == s[i] || s[i] == s[i+1] {
            return false;
        }
        proof {
            reveal_three_distinct_lemma(s@, i);
            assert(three_distinct_spec(s@, i));
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {}
}