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
    let mut i: int = 0;
    let mut sum: int = 0;
    let mut max: int = 0;

    if N > 0 {
        max = a[0];
    }

    while i < N
        invariant 
            0 <= i, 
            i <= N,
            sum == {
                let mut s = 0;
                let mut k = 0;
                while k < i 
                    invariant
                        0 <= k,
                        k <= i,
                        s == (0..k).fold(0, |acc, idx| acc + a[idx])
                {
                    s = s + a[k];
                    k = k + 1;
                }
                s
            },
            N > 0 ==> (
                max == {
                    let mut m = a[0];
                    let mut k = 1;
                    while k < i 
                        invariant
                            1 <= k,
                            k <= i,
                            m == (1..k).fold(a[0], |current_max, idx| if a[idx] > current_max { a[idx] } else { current_max }),
                        // Trigger for a[idx]
                        #[trigger] a[k],
                    {
                        if a[k] > m {
                            m = a[k];
                        }
                        k = k + 1;
                    }
                    m
                }
            ),
            N == 0 ==> max == 0,
            forall|k: int| 0 <= k && k < i ==> a[k] <= max,
            sum <= i * max,
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