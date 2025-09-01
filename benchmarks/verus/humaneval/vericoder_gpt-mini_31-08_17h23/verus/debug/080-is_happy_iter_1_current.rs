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
    // impl-start
    let n: int = s.len() as int;
    if n < 3 {
        return false;
    }
    let mut i: int = 1;
    while i <= n - 2 {
        invariant 1 <= i && i <= n;
        invariant forall |j: int| 0 < j && j < i ==> three_distinct_spec(s@, j);
        let a = s@[i - 1];
        let b = s@[i];
        let c = s@[i + 1];
        if !(a != b && b != c && a != c) {
            return false;
        }
        i = i + 1;
    }
    true
    // impl-end
}
// </vc-code>

fn main() {}
}