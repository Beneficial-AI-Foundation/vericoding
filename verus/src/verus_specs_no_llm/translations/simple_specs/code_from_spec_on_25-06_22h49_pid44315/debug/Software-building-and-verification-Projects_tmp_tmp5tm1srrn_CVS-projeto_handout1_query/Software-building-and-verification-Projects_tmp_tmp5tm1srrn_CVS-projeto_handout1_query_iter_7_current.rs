use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i as usize] + sum(a, i + 1, j)
    }
}

// Helper lemma to prove the additive property of sum
proof fn sum_additive(a: Vec<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= a.len()
    ensures sum(a, i, k) == sum(a, i, j) + sum(a, j, k)
    decreases k - i
{
    if i >= k {
        // Base case: i == k, so sum(a, i, k) == 0
        assert(sum(a, i, k) == 0);
        assert(sum(a, i, j) == 0);
        assert(sum(a, j, k) == 0);
    } else if i >= j {
        // Case: i == j
        assert(sum(a, i, j) == 0);
        assert(sum(a, i, k) == sum(a, j, k));
    } else {
        // Recursive case: i < j <= k
        assert(sum(a, i, k) == a[i as usize] + sum(a, i + 1, k));
        assert(sum(a, i, j) == a[i as usize] + sum(a, i + 1, j));
        sum_additive(a, i + 1, j, k);
        assert(sum(a, i + 1, k) == sum(a, i + 1, j) + sum(a, j, k));
    }
}

fn main() {
}

fn query(a: Vec<int>, i: int, j: int) -> (res: int)
    requires
        0 <= i <= j <= a.len(),
        a.len() < usize::MAX,
        j < usize::MAX
    ensures
        res == sum(a, i, j)
{
    let mut sum_val = 0;
    let mut k = i;
    
    while k < j
        invariant
            i <= k <= j,
            sum_val == sum(a, i, k),
            0 <= k <= j,
            k < usize::MAX,
            j < usize::MAX,
            a.len() < usize::MAX
        decreases j - k
    {
        // Prove bounds for array access
        assert(k < j);
        assert(k >= 0);
        assert(k < a.len() as int);
        
        // Prove that k can be safely converted to usize
        assert(k >= 0 && k < a.len() as int);
        assert(a.len() < usize::MAX);
        assert(k < usize::MAX);
        
        // Prove that k + 1 won't overflow
        assert(k + 1 <= j);
        assert(j < usize::MAX);
        assert(k + 1 < usize::MAX);
        
        // Use the additive property to help verification
        proof {
            sum_additive(a, i, k, k + 1);
            assert(sum(a, i, k + 1) == sum(a, i, k) + sum(a, k, k + 1));
            assert(sum(a, k, k + 1) == a[k as usize]);
        }
        
        sum_val = sum_val + a[k as usize];
        k = k + 1;
    }
    
    sum_val
}

}