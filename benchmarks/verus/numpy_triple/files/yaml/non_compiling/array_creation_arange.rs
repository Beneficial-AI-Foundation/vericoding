/* Return evenly spaced values within a given interval [start, stop) with given step.
Specification: arange generates evenly spaced values from start to stop (exclusive) with given step.
Each element at index i has value start + i * step, and all values are within bounds. */

use vstd::prelude::*;

verus! {
fn arange(n: usize, start: f64, stop: f64, step: f64) -> (result: Vec<f64>)
    requires 
        step != 0.0,
    ensures 
        result.len() == n,
        n == 0 ==> ((step > 0.0 && start >= stop) || (step < 0.0 && start <= stop)),
        n > 0 ==> {
            &&& (forall|i: int| 0 <= i < n ==> result[i] == start + (i as f64) * step)
            &&& (step > 0.0 ==> (start < stop && forall|i: int| 0 <= i < n ==> result[i] < stop))
            &&& (step < 0.0 ==> (start > stop && forall|i: int| 0 <= i < n ==> result[i] > stop))
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}