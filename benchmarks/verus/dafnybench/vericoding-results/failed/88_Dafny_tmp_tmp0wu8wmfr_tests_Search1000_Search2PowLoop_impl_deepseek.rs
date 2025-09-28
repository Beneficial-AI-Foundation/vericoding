use vstd::prelude::*;

verus! {

// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Verus version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  

// Is2Pow(n) is true iff n==2^k for some k>=0.
spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
spec fn gap(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        (n - 1) / 2
    }
}

proof fn lemma_gap_properties(n: int)
    requires
        n >= 0,
    ensures
        gap(n) == (n - 1) / 2,
        gap(n) >= -1,
    decreases n
{
    if n > 0 {
        lemma_gap_properties(n - 1);
    }
}

proof fn lemma_2_pow_minus_one_properties(n: int)
    requires
        is_2_pow(n + 1),
    ensures
        n >= 0,
    {
        assert(n >= 0) by {
            if n < 0 {
                assert(!is_2_pow(n + 1));
            }
        }
    }

proof fn lemma_step_invariant_maintained(i: int, n: int, x: i32, a: Seq<i32>, k: int, step_size: int, candidate: int)
    requires
        i <= k <= i + n,
        step_size >= 0,
        candidate == if a[k] < x { k + 1 } else { k },
        0 <= step_size < n,
        forall|p: int, q: int| i <= p < q < (i + n) && 0 <= p < a.len() && 0 <= q < a.len() ==> 
            a[p] <= a[q],
    ensures
        i <= candidate <= i + n,
        forall|r: int| i <= r < candidate && 0 <= r < a.len() ==> a[r] < x,
        forall|r: int| candidate <= r < (i + n) && 0 <= r < a.len() ==> a[r] >= x,
{
    if a[k] < x {
        assert forall|r: int| i <= r < candidate implies a[r] < x by {
            if r < k {
                assert(a[r] <= a[k]);
                assert(a[r] < x);
            } else if r == k {
                assert(a[r] < x);
            }
        }
        assert forall|r: int| candidate <= r < (i + n) implies a[r] >= x by {
            assert(a[r] >= a[k]);
        }
    } else {
        assert forall|r: int| i <= r < candidate implies a[r] < x by {
        }
        assert forall|r: int| candidate <= r < (i + n) implies a[r] >= x by {
            if r == k {
                assert(a[r] >= x);
            } else if r > k {
                assert(a[r] >= a[k]);
                assert(a[r] >= x);
            }
        }
    }
}

proof fn lemma_step_size_properties(step_size: int)
    requires
        step_size >= 0,
    ensures
        exists|s: int| #[trigger] s >= 0 && s == step_size,
{
    assert(#[trigger] step_size >= 0);
}
// </vc-helpers>

// <vc-spec>
fn search_2_pow_loop(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i <= i + n <= a.len(),
        forall|p: int, q: int| i <= p < q < (i + n) && 0 <= p < a.len() && 0 <= q < a.len() ==> 
            a@[p] <= a@[q],
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        forall|r: int| i <= r < k && 0 <= r < a.len() ==> a@[r] < x,
        forall|r: int| k <= r < (i + n) && 0 <= r < a.len() ==> a@[r] >= x,
// </vc-spec>
// <vc-code>
{
    let mut k = i + n / 2;
    let mut step_size = n / 2;
    
    proof {
        lemma_2_pow_minus_one_properties(n as int);
        lemma_step_size_properties(step_size as int);
    }
    
    while step_size > 0
        invariant
            step_size >= 0,
            i <= k <= i + n,
            exists|s: int| #[trigger] s >= 0 && s == step_size,
            forall|r: int| i <= r < k && 0 <= r < a.len() ==> a[r] < x,
            forall|r: int| k <= r < (i + n) && 0 <= r < a.len() ==> a[r] >= x,
        decreases step_size
    {
        let next_step = step_size / 2;
        
        proof {
            lemma_gap_properties(step_size as int);
            lemma_step_size_properties(next_step as int);
        }
        
        let candidate = if a[k] < x { k + next_step + 1 } else { k - next_step - 1 };
        
        proof {
            lemma_step_invariant_maintained(i as int, n as int, x, a@, k as int, step_size as int, candidate as int);
        }
        
        k = candidate;
        step_size = next_step;
    }
    
    k
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

fn main() {}

}