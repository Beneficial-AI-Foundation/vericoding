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
proof lemma_sum_le_n_times_max(a: Seq<int>, max: int, n: int)
    requires
        0 <= n,
        n <= a.len(),
        forall|k: int| 0 <= k && k < n ==> a[k] <= max,
    ensures
        seq_sum(a.subrange(0, n as int)) <= n * max
{
    if n == 0 {
        assert(seq_sum(a.subrange(0, 0)) == 0);
    } else {
        lemma_sum_le_n_times_max(a, max, n - 1);
        assert(a[n - 1] <= max);
        assert(seq_sum(a.subrange(0, n)) == seq_sum(a.subrange(0, n - 1)) + a[n - 1]);
        assert(seq_sum(a.subrange(0, n - 1)) <= (n - 1) * max);
        assert(seq_sum(a.subrange(0, n)) <= (n - 1) * max + max);
    }
}

spec fn seq_sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + seq_sum(s.subrange(1, s.len() as int))
    }
}

spec fn seq_max(s: Seq<int>) -> int
    requires s.len() > 0,
    decreases s.len(),
{
    if s.len() == 1 {
        s[0]
    } else {
        let sub_max = seq_max(s.subrange(1, s.len() as int));
        if s[0] > sub_max { s[0] } else { sub_max }
    }
}
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
        invariant 
            0 <= i && i <= N,
            sum == seq_sum(a@.subrange(0, i)),
            max == (if i > 0 then seq_max(a@.subrange(0, i)) else 0),
            forall|k: int| 0 <= k && k < i ==> a@[k] <= max,
        decreases N - i,
    {
        let x = a[i as usize];
        proof {
            assert(a@[i] == x);
        }
        if x > max {
            max = x;
        }
        sum = sum + x;
        i = i + 1;
        
        proof {
            if i > 0 {
                assert forall|k: int| 0 <= k && k < i implies a@[k] <= max by {
                    if k == i - 1 {
                        assert(a@[k] == x);
                        if old(max) < x {
                            assert(a@[k] <= max);
                        } else {
                            assert(a@[k] <= old(max));
                            assert(old(max) <= max);
                        }
                    } else {
                        assert(k < i - 1);
                        assert(a@[k] <= old(max));
                        assert(old(max) <= max);
                    }
                }
                assert(seq_max(a@.subrange(0, i)) == max);
            }
        }
    }
    
    proof {
        lemma_sum_le_n_times_max(a@, max, N);
    }
    
    (sum, max)
}
// </vc-code>

fn main() {}

}