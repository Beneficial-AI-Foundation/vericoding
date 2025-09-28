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
    let a_seq = a@;
    let mut sum = 0;
    let mut max_val = 0;
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            0 <= sum,
            0 <= max_val,
            forall|k: int| #[trigger(a_seq@[k])] 0 <= k && k < N ==> 0 <= a_seq@[k],
            forall|j: int| #[trigger(a_seq@[j])] 0 <= j && j < i ==> a_seq@[j] <= max_val,
            sum <= i * max_val
        decreases N - i
    {
        sum = sum + a[i];
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    (sum, max_val)
}
// </vc-code>

fn main() {}

}