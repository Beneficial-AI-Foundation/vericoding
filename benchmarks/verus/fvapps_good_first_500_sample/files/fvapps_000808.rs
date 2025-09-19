// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate_maintenance_due(n: usize, payments: Vec<String>) -> (result: usize)
    ensures
        n == 0 ==> result == 0,
        payments.len() == 0 ==> result == 0
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
    // Assurance level: guarded_and_plausible

    // let result1 = calculate_maintenance_due(2, vec!["1".to_string(), "1".to_string()]);
    // assert!(result1 == 0);

    // let result2 = calculate_maintenance_due(2, vec!["0".to_string(), "0".to_string()]);
    // assert!(result2 == 2200);

    // let result3 = calculate_maintenance_due(3, vec!["0".to_string(), "1".to_string(), "0".to_string()]);
    // assert!(result3 == 2300);
}