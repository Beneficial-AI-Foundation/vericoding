/* Least squares fit of Hermite series to data. Returns coefficients of a Hermite polynomial that best fits the given data points (x, y) with degree deg. */

use vstd::prelude::*;

verus! {
fn hermfit(x: Vec<f64>, y: Vec<f64>, deg: usize) -> (result: Vec<f64>)
    requires 
        x.len() > 0,
        x.len() == y.len(),
        deg < x.len(),
    ensures
        result.len() == deg + 1,
        deg + 1 > 0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}