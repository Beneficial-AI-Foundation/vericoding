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
    if s.len() < 3 {
        return false;
    }

    let mut i: usize = 1;

    #[invariant(
        1 <= i,
        i <= s.len(), // i can reach s.len()
        forall |j: int| 0 < j && j < i as int && j + 1 < s.len() ==>
            three_distinct_spec_for_all(s@, j)
    )]
    while (i as int) + 1 < (s.len() as int)
    {
        let current_char = s[i];
        let prev_char = s[i-1];
        let next_char = s[i+1];

        if prev_char == current_char || current_char == next_char || prev_char == next_char {
            return false;
        }
        i = i + 1;
    }

    // After the loop, we need to prove that three_distinct_spec holds for all relevant 'i'.
    // The loop invariant ensures it for i < old_i (current loop iteration's i).
    // We also need to consider the last element checked.
    proof {
        assert(forall |j: int| 0 < j && j + 1 < s.len() ==> three_distinct_spec_for_all(s@, j));
    }

    true
}
// </vc-code>

fn main() {}
}