// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(sides: Seq<int>) -> bool {
    sides.len() >= 3 && forall|i: int| 0 <= i < sides.len() ==> sides[i] > 0
}

spec fn can_form_polygon(sides: Seq<int>) -> bool
    recommends valid_input(sides)
{
    let sorted_sides = quicksort(sides);
    let longest = sorted_sides[sorted_sides.len() - 1];
    let sum_of_others = sum_except_last(sorted_sides);
    sum_of_others > longest
}

spec fn quicksort(s: Seq<int>) -> Seq<int> {
    seq![]
}

spec fn filter(s: Seq<int>, pred: spec_fn(int) -> bool) -> Seq<int> {
    seq![]
}

spec fn sum_except_last(s: Seq<int>) -> int
    recommends s.len() >= 1
{
    0
}

proof fn filter_preserves_inclusion(s: Seq<int>, pred: spec_fn(int) -> bool)
    ensures forall|x: int| #![auto] filter(s, pred).contains(x) ==> s.contains(x)
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(sides: Seq<int>) -> (result: String)
    requires
        valid_input(sides),
    ensures
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
        (result@ == seq!['Y', 'e', 's']) == can_form_polygon(sides),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No".to_string()
}
// </vc-code>


}

fn main() {}