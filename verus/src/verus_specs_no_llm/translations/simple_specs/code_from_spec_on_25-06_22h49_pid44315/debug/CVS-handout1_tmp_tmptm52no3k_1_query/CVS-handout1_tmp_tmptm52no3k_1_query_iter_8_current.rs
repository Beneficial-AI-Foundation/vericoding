use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i] + sum(a, i + 1, j)
    }
}

// Helper lemma to prove the recursive property of sum
proof fn sum_property(a: Seq<int>, i: int, k: int)
    requires
        i <= k,
        0 <= i,
        0 <= k < a.len()
    ensures
        sum(a, i, k + 1) == sum(a, i, k) + a[k]
    decreases k + 1 - i
{
    if i == k {
        // Base case: sum(a, i, k+1) == a[k] and sum(a, i, k) == 0
        assert(sum(a, i, k) == 0);
        assert(sum(a, i, k + 1) == a[k] + sum(a, k + 1, k + 1));
        assert(sum(a, k + 1, k + 1) == 0);
        assert(sum(a, i, k + 1) == a[k]);
    } else {
        // Recursive case: i < k
        sum_property(a, i + 1, k);
        assert(sum(a, i + 1, k + 1) == sum(a, i + 1, k) + a[k]);
        
        // Expand the definitions
        assert(sum(a, i, k + 1) == a[i] + sum(a, i + 1, k + 1));
        assert(sum(a, i, k) == a[i] + sum(a, i + 1, k));
        
        // Use the inductive hypothesis
        assert(sum(a, i, k + 1) == a[i] + sum(a, i + 1, k) + a[k]);
        assert(sum(a, i, k + 1) == sum(a, i, k) + a[k]);
    }
}

fn main() {
}

fn query(a: Vec<int>, i: usize, j: usize) -> (res: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        res == sum(a@, i as int, j as int)
{
    let mut sum_val = 0;
    let mut k = i;
    
    while k < j
        invariant
            i <= k <= j,
            sum_val == sum(a@, i as int, k as int),
            0 <= i <= a.len(),
            0 <= k <= a.len(),
            0 <= j <= a.len()
        decreases j - k
    {
        // Use the helper lemma to prove the recursive property
        proof {
            sum_property(a@, i as int, k as int);
        }
        
        sum_val = sum_val + a[k];
        k = k + 1;
    }
    
    sum_val
}

}