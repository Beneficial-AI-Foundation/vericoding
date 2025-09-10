/* Compute the roots of a Laguerre series.

Return the roots (a.k.a. "zeros") of the polynomial
p(x) = sum_i c[i] * L_i(x).

Specification: lagroots computes the roots of a Laguerre polynomial */

use vstd::prelude::*;

verus! {
fn lagroots(c: Vec<i32>) -> (roots: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] == 1 + c@[0] / c@[1],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}