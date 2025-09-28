// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed potential overflow and a type error in a loop invariant */
    let mut b: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            b@.len() == i as int,
            b@ == x@.subrange(0, i as int),
        decreases x.len() - i
    {
        b.push(x[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < y.len()
        invariant
            0 <= j <= y.len(),
            b@.len() == x.len() as int + j as int,
            b@ == x@ + y@.subrange(0, j as int),
        decreases y.len() - j
    {
        b.push(y[j]);
        j = j + 1;
    }

    b
}
// </vc-code>

}
fn main() {}