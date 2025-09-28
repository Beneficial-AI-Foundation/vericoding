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
    let n = N;
    let mut i: int = 0;
    let mut s: int = 0;
    let mut m: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            a.len() == n,
            s <= i * m,
        decreases n - i
    {
        let ai = a[i];
        let old_m = m;
        if m < ai {
            m = ai;
        }
        assert(m >= old_m);
        assert(ai <= m);

        let old_s = s;
        // From invariant: old_s <= i * old_m
        assert(i * old_m <= i * m);
        assert(old_s <= i * m);

        s = old_s + ai;
        assert(s <= i * m + m);
        assert(i * m + m == (i + 1) * m);

        i = i + 1;
    }
    assert(i == n);
    (s, m)
}
// </vc-code>

fn main() {}

}