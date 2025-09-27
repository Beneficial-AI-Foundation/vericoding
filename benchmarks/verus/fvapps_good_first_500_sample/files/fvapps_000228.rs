// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_poisoned_duration(time_series: Vec<i32>, duration: i32) -> (result: i32)
    requires duration > 0,
    ensures 
        result >= 0,
        time_series.len() == 0 ==> result == 0,
        time_series.len() > 0 ==> result <= (time_series[time_series.len() - 1] - time_series[0]) + duration
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
    // Apps difficulty: interview
    // Assurance level: guarded
    
    // Example test cases:
    // find_poisoned_duration([1, 4], 2) should return 4
    // find_poisoned_duration([1, 2], 2) should return 3
    // find_poisoned_duration([], 5) should return 0
}