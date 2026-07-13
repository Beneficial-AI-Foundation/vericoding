// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_ice_cream(num_flavors: nat, costs: &Vec<nat>, weight: nat, num_required: nat) -> (result: Option<nat>)
    requires 
        num_flavors > 0,
        forall|i: int| 0 <= i < costs.len() ==> costs[i] > 0,
        weight > 0,
        num_required > 0,
    ensures
        match result {
            Option::None => weight < num_required || num_flavors < num_required,
            Option::Some(cost) => cost >= 0 && weight >= num_required && num_flavors >= num_required
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Option::None
    // impl-end
}
// </vc-code>


}
fn main() {}