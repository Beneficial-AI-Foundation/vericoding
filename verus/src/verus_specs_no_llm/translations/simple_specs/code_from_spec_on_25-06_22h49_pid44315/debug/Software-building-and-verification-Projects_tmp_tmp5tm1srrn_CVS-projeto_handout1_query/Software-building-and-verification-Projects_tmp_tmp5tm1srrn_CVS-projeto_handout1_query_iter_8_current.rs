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
            a.len() < usize::MAX,
            k <= a.len()
        decreases j - k
    {
        // Prove bounds for array access
        assert(k < j);
        assert(k >= 0);
        assert(k < a.len() as int);
        
        // Prove that k can be safely converted to usize
        assert(k >= 0);
        assert(k < a.len() as int);
        assert(a.len() <= usize::MAX);
        
        // Prove that k + 1 won't overflow
        assert(k + 1 <= j);
        assert(j < usize::MAX);
        
        // Store the current value for the proof
        let old_sum = sum_val;
        let old_k = k;
        
        // Access the array element
        let elem = a[k as usize];
        sum_val = sum_val + elem;
        k = k + 1;
        
        // Use the additive property to help verification
        proof {
            assert(old_k < j);
            assert(sum(a, old_k, old_k + 1) == a[old_k as usize]);
            sum_additive(a, i, old_k, old_k + 1);
            assert(sum(a, i, old_k + 1) == sum(a, i, old_k) + sum(a, old_k, old_k + 1));
            assert(sum(a, i, old_k + 1) == old_sum + elem);
            assert(k == old_k + 1);
            assert(sum_val == old_sum + elem);
        }
    }
    
    sum_val
}

}