/* Return elements chosen from x or y depending on condition.
For each position i, if condition[i] is True, take x[i], otherwise take y[i].

Specification: numpy_where returns an array where elements are chosen from x when condition is True,
and from y when condition is False. */

use vstd::prelude::*;

verus! {
fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        condition.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            (condition[i] ==> result[i] == x[i]) &&
            (!condition[i] ==> result[i] == y[i])
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}