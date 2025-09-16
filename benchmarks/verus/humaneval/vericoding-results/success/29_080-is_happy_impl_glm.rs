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
proof fn three_distinct_lemma(s: Seq<char>, i: int)
    requires
        0 < i && i + 1 < s.len(),
    ensures
        three_distinct_spec(s, i) <==> (s[i-1] != s[i] && s[i] != s[i+1] && s[i] != s[i+1]),
{
    reveal(three_distinct_spec);
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
    let n = s.len();
    if n < 3 {
        return false;
    }
    let mut i = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            forall|j: int| 1 <= j < i ==> three_distinct_spec(s@, j),
        decreases n - i,
    {
        if !(s[i-1] != s[i] && s[i] != s[i+1] && s[i] != s[i+1]) {
            proof {
                three_distinct_lemma(s@, i as int);
            }
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}