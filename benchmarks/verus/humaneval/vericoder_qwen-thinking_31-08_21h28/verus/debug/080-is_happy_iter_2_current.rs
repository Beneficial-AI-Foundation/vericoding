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
    let n = s.len();
    if n < 3 {
        return false;
    }
    let mut i = 1;
    while i < n - 1 {
        invariant (i >= 1) && (i <= n - 1) && 
                (forall |j: int| 1 <= j < i ==> #[trigger(three_distinct_spec(s@, j))] three_distinct_spec(s@, j))
        if !three_distinct_spec(s@, i) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {}
}