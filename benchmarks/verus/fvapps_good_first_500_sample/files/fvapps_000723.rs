// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn check_rocket_stability_spec(coeff: Seq<i32>) -> u32 
{
    if coeff.len() == 0 { 1 }
    else if coeff.len() == 1 { 1 }
    else if forall|i: int| 0 <= i < coeff.len() ==> coeff[i] == 0 { 1 }
    else { 0 } // placeholder specification
}

fn check_rocket_stability(coeff: Vec<i32>) -> (result: u32)
    ensures result == 0 || result == 1
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


proof fn check_rocket_binary(coeff: Vec<i32>)
    ensures check_rocket_stability(coeff) == 0 || check_rocket_stability(coeff) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn zeros_stable(zeros: Vec<i32>)
    requires forall|i: int| 0 <= i < zeros.len() ==> zeros[i] == 0,
    ensures check_rocket_stability(zeros) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn single_coeff_stable(coeff: Vec<i32>)
    requires coeff.len() == 1,
    ensures check_rocket_stability(coeff) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn copy_safety(coeff: Vec<i32>)
    ensures check_rocket_stability(coeff) == 0 || check_rocket_stability(coeff) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // check_rocket_stability([10, 12, 4, 5, 3]) should output 0
    // check_rocket_stability([0, 0, 0]) should output 1
    // check_rocket_stability([5]) should output 1
}