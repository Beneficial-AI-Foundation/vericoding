// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_tiring(hours: nat) -> bool {
    hours > 8
}

spec fn count_tiring_days(hours: Seq<nat>) -> nat
    decreases hours.len()
{
    if hours.len() == 0 {
        0nat
    } else {
        (if is_tiring(hours[0]) { 1nat } else { 0nat }) + count_tiring_days(hours.skip(1))
    }
}

spec fn is_well_performing_interval(hours: Seq<nat>) -> bool {
    let tiring_days = count_tiring_days(hours);
    let non_tiring_days = hours.len() - tiring_days;
    tiring_days > non_tiring_days
}

fn longest_wpi(hours: Vec<nat>) -> (result: nat)
    requires 
        hours.len() >= 1,
        hours.len() <= 10000,
        forall|i: int| 0 <= i < hours.len() ==> hours[i] <= 16,
    ensures 
        result >= 0,
        result <= hours.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![9, 9, 6, 0, 6, 6, 9];
    // let result1 = longest_wpi(test1);
    // println!("Test 1 result: {}", result1);
    
    // let test2 = vec![6, 6, 6];
    // let result2 = longest_wpi(test2);
    // println!("Test 2 result: {}", result2);
    
    // let test3 = vec![9, 9, 9];
    // let result3 = longest_wpi(test3);
    // println!("Test 3 result: {}", result3);
}