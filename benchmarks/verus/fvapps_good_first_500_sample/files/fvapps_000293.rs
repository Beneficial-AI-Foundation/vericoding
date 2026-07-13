// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn least_ops_express_target_spec(x: nat, target: nat) -> nat;

fn least_ops_express_target(x: usize, target: usize) -> (result: usize)
    requires 
        x >= 2,
        x <= 100,
        target >= 1,
        target <= 200000000,
    ensures
        result >= 0,
        result == least_ops_express_target_spec(x as nat, target as nat),
        (x == target) ==> (result <= 2),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn output_is_non_negative(x: usize, target: usize)
    requires 
        x >= 2,
        x <= 100,
        target >= 1,
        target <= 1000000,
    ensures
        least_ops_express_target_spec(x as nat, target as nat) >= 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn target_equals_x_minimal_ops(x: usize)
    requires 
        x >= 2,
        x <= 100,
    ensures
        least_ops_express_target_spec(x as nat, x as nat) <= 2,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn power_requires_fewer_ops(x: usize, power: usize)
    requires 
        x >= 2,
        x <= 20,
        power >= 2,
        power <= 5,
    ensures
        least_ops_express_target_spec(x as nat, pow(x as int, power as nat) as nat) <= least_ops_express_target_spec(x as nat, pow(x as int, power as nat) as nat + 1),
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded
}