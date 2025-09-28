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
spec fn spec_sum(s: Seq<int>, n: int) -> int
    requires n >= 0, n <= s.len()
    decreases n
{
    if n <= 0 {
        0
    } else {
        spec_sum(s, n - 1) + s[n - 1]
    }
}

spec fn spec_max(s: Seq<int>, n: int) -> int
    requires n > 0, n <= s.len()
    decreases n
{
    if n == 1 {
        s[0]
    } else {
        let prev_max = spec_max(s, n - 1);
        if s[n - 1] > prev_max {
            s[n - 1]
        } else {
            prev_max
        }
    }
}

proof fn lemma_sum_le_n_times_max(s: Seq<int>, n: int)
    requires 
        n > 0,
        n <= s.len(),
        forall|k: int| 0 <= k && k < s.len() ==> 0 <= s[k],
    ensures 
        spec_sum(s, n) <= n * spec_max(s, n)
    decreases n
{
    if n == 1 {
        assert(spec_sum(s, 1) == s[0]);
        assert(spec_max(s, 1) == s[0]);
        assert(spec_sum(s, 1) <= 1 * spec_max(s, 1));
    } else {
        lemma_sum_le_n_times_max(s, n - 1);
        assert(spec_sum(s, n - 1) <= (n - 1) * spec_max(s, n - 1));
        
        let prev_max = spec_max(s, n - 1);
        let current = s[n - 1];
        let new_max = if current > prev_max { current } else { prev_max };
        
        assert(spec_max(s, n) == new_max);
        assert(spec_sum(s, n) == spec_sum(s, n - 1) + current);
        
        if current > prev_max {
            assert(spec_sum(s, n - 1) <= (n - 1) * prev_max);
            assert(prev_max < current);
            assert(spec_sum(s, n - 1) < (n - 1) * current);
            assert(0 <= current);
            assert(spec_sum(s, n) <= (n - 1) * current + current);
            assert(spec_sum(s, n) <= n * current);
            assert(spec_sum(s, n) <= n * new_max);
        } else {
            assert(current <= prev_max);
            assert(spec_sum(s, n) == spec_sum(s, n - 1) + current);
            assert(spec_sum(s, n) <= (n - 1) * prev_max + prev_max);
            assert(spec_sum(s, n) <= n * prev_max);
            assert(spec_sum(s, n) <= n * new_max);
        }
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
    if N == 0 {
        return (0, 0);
    }
    
    let mut sum: int = a[0];
    let mut max: int = a[0];
    let mut i: usize = 1;
    
    while i < N as usize
        invariant
            1 <= i,
            i <= N as usize,
            a.len() == N as usize,
            N > 0,
            forall|k: int| 0 <= k && k < N ==> #[trigger] (0 <= a[k]),
            sum == spec_sum(a@, i as int),
            max == spec_max(a@, i as int),
            sum <= (i as int) * max,
    {
        let old_sum = sum;
        let old_max = max;
        let old_i = i;
        
        sum = sum + a[i];
        if a[i] > max {
            max = a[i];
        }
        
        proof {
            assert(a@.len() == N);
            assert(old_i < N);
            assert(spec_sum(a@, (old_i + 1) as int) == spec_sum(a@, old_i as int) + a[old_i]);
            
            if a[old_i] > old_max {
                assert(spec_max(a@, (old_i + 1) as int) == a[old_i]);
                assert(max == a[old_i]);
                assert(old_sum <= old_i as int * old_max);
                assert(0 <= a[old_i]);
                assert(old_sum <= old_i as int * a[old_i]);
                assert(sum == old_sum + a[old_i]);
                assert(sum <= old_i as int * a[old_i] + a[old_i]);
                assert(sum <= (old_i + 1) as int * a[old_i]);
                assert(sum <= (old_i + 1) as int * max);
            } else {
                assert(spec_max(a@, (old_i + 1) as int) == old_max);
                assert(max == old_max);
                assert(old_sum <= old_i as int * old_max);
                assert(a[old_i] <= old_max);
                assert(sum == old_sum + a[old_i]);
                assert(sum <= old_i as int * old_max + old_max);
                assert(sum <= (old_i + 1) as int * old_max);
                assert(sum <= (old_i + 1) as int * max);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == N);
        lemma_sum_le_n_times_max(a@, N as int);
    }
    
    (sum, max)
}
// </vc-code>

fn main() {}

}