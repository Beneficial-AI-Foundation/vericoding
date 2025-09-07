/* Create a 1D open grid from start to stop with n evenly spaced points.
This is a simplified version of ogrid that handles the common case of
creating a single evenly-spaced vector (like ogrid[start:stop:nj]).

Specification: ogrid creates n evenly spaced points from start to stop (inclusive).
When n > 1, the spacing between consecutive points is (stop - start) / (n - 1).
For n = 1, the single point is at start. */

use vstd::prelude::*;

verus! {
fn ogrid(start: f32, stop: f32, n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures 
        result.len() == n,
        (n == 1 ==> result[0] == start),
        (n > 1 ==> result[0] == start),
        (n > 1 ==> result[n - 1] == stop),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}