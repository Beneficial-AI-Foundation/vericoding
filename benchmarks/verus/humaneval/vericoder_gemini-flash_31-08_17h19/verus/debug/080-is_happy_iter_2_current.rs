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
spec fn three_distinct_spec_for_all(s: Seq<char>, i: int) -> bool {
    s.len() >= 3 && 0 < i && i + 1 < s.len() ==>
        (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
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
    // impl-start
    if s.len() < 3 {
        return false;
    }

    let mut i: int = 1;

    #[verifier::loop_invariant(
        1 <= i,
        i <= s.len(),
        forall |j: int| 0 < j && j < i && j + 1 < s.len() ==> 
            (s@[j - 1] != s@[j]) && (s@[j] != s@[j + 1]) && (s@[j - 1] != s@[j + 1])
    )]
    while (i as usize + 1) < s.len()
    {
        if s@[i as int - 1] == s@[i as int] || s@[i as int] == s@[i as int + 1] || s@[i as int - 1] == s@[i as int + 1] {
            return false;
        }
        i = i + 1;
    }

    // After the loop, we need to prove that three_distinct_spec holds for all relevant 'i'.
    // The loop invariant ensures it for i < old_i (current loop iteration's i).
    // We also need to consider the last element checked.
    assert(forall |j: int| 0 < j && j + 1 < s.len() ==> three_distinct_spec(s@, j));

    true
    // impl-end
}
// </vc-code>

fn main() {}
}