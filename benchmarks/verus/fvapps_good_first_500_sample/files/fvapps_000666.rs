// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_corner_point(x: usize, y: usize, n: usize) -> bool {
    (x == 0 && y == 0) || (x == 0 && y == n-1) || 
    (x == n-1 && y == 0) || (x == n-1 && y == n-1)
}

fn assess_lights(k: usize, n: usize, points: Vec<(usize, usize)>) -> (result: &'static str)
    requires 
        1 <= k <= 100,
        1 <= n <= 1000000000,
        points.len() == k,
        forall|i: int| 0 <= i < points.len() ==> #[trigger] points[i].0 < n && #[trigger] points[i].1 < n,
    ensures 
        result == "yes" || result == "no",
        /* If k > 3, then result is "yes" */
        k > 3 ==> result == "yes",
        /* If any point is a corner, then result is "yes" */
        (exists|i: int| 0 <= i < points.len() && #[trigger] is_corner_point(points[i].0, points[i].1, n)) ==> result == "yes",
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "no"
    // impl-end
}
// </vc-code>


}
fn main() {
    // Example usage:
    // let result1 = assess_lights(2, 10, vec![(0, 0), (1, 0)]);
    // println!("{}", result1); // Should print "yes"
    // 
    // let result2 = assess_lights(2, 10, vec![(1, 2), (1, 1)]);
    // println!("{}", result2); // Should print "no"
    //
    // let result3 = assess_lights(3, 5, vec![(0, 0), (4, 2), (2, 4)]);
    // println!("{}", result3); // Should print "yes"
}