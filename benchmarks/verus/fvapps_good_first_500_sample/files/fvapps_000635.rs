// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_second_largest(l: Vec<i32>) -> (result: i32)
    requires l.len() >= 3,
    ensures
        exists|x: i32| l@.contains(x) && x > result,
        exists|x: i32| l@.contains(x) && x < result,
        l@.contains(result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: guarded */

// #guard_msgs in
// #eval find_second_largest [120, 11, 400]

// #guard_msgs in
// #eval find_second_largest [10213, 312, 10]

// #guard_msgs in
// #eval find_second_largest [10, 3, 450]

}

fn main() {}