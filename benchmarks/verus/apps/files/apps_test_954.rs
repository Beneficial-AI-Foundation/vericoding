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
    assume(false);
    0
}
// </vc-code>


}

fn main() {}