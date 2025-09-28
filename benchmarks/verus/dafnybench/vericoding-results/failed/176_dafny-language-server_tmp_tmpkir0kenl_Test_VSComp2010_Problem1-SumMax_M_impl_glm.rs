use vstd::prelude::*;

verus! {

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn M(N: int, a: &[int]) -> (result: (int, int))
    requires 
        0 <= N,
        a.len() == N,
        forall|k: int| 0 <= k && k < N ==> 0 <= a[k],
    ensures 
        result.0 <= N * result.1;
// </vc-spec>
// <vc-code>
{
    let mut sum: int = 0;
    let mut max: int = 0;
    let mut i: int = 0;

    while i < N
        invariant 0 <= i <= N
        invariant sum <= i * max
        invariant max == (if i == 0 { 0 } else { a@.subrange(0, i).max() })
    {
        sum = sum + a[i];
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }

    (sum, max)
}
// </vc-code>

fn main() {}

}