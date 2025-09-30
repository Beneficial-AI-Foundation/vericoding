// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn cyclic_shift_forward(s: Seq<char>) -> Seq<char>
{
    if s.len() > 0 { s.subrange(1, s.len() as int).add(seq![s[0]]) } else { s }
}

spec fn valid_input(s: Seq<char>) -> bool
{
    s.len() > 0
}

spec fn apply_shifts(s: Seq<char>, steps: nat) -> Seq<char>
    decreases steps
{
    if s.len() > 0 && steps > 0 { cyclic_shift_forward(apply_shifts(s, (steps - 1) as nat)) }
    else if s.len() > 0 { s }
    else { s }
}

spec fn all_distinct_cyclic_shifts(s: Seq<char>) -> nat
{
    if s.len() > 0 { s.len() } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_all_distinct_cyclic_shifts_len(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        all_distinct_cyclic_shifts(s) == s.len(),
{
    assert(all_distinct_cyclic_shifts(s) == s.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@),
    ensures 
        1 <= result <= s.len(),
        result == all_distinct_cyclic_shifts(s@),
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    proof {
        assert(valid_input(s@));
        assert(s.len() > 0);
        lemma_all_distinct_cyclic_shifts_len(s@);
        assert(all_distinct_cyclic_shifts(s@) == s.len());
        assert(1 <= s.len());
    }
    n
}
// </vc-code>


}

fn main() {}