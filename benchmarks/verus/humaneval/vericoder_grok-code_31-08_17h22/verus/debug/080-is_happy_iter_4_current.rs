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
    if s.len() < 3 {
        return false;
    }
    let len = s.len();
    for i: int in 1..(len - 1)
        invariant
            1 <= i <= len - 2,
            (forall |k: int| #[trigger] ((1 <= k <= i && 0 < k && k + 1 < len)) ==> (
                s@[k - 1] != s@[k] &&
                s@[k] != s@[k + 1] &&
                s@[k - 1] != s@[k + 1]
            ))
    {
        if s@[i] == s@[i - 1] || s@[i] == s@[i + 1] || s@[i - 1] == s@[i + 1] {
            return false;
        }
    }
    proof {
        assert(s.len() >= 3);
        assert(forall |i_: int| #[trigger] ((0 < i_ && i_ + 1 < s.len())) ==> (
            s@[i_ - 1] != s@[i_] &&
            s@[i_] != s@[i_ + 1]
        ));
    }
    true
}
// </vc-code>

fn main() {}
}