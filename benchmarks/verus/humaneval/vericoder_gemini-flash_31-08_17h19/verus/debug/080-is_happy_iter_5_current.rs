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

    #[verifier::loop_invariant_when(
        (i as int) + 1 < (s.len() as int)
        imply (
            1 <= i && i <= s.len() &&
            forall |j: int| 0 < j && (j as nat) < i && (j as nat) + 1 < s.len() ==>
                three_distinct_spec_for_all(s@, j)
        )
    )]
    #[verifier::loop_termination_block]
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

    proof {
        assert(forall |j: int| 0 < j && (j as nat) + 1 < s.len() ==> three_distinct_spec_for_all(s@, j));
    }

    true
}
// </vc-code>

fn main() {}
}