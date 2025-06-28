use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i] + sum(a, i + 1, j)
    }
}

proof fn lemma_sum_extend(a: Vec<int>, i: int, j: int)
    requires 0 <= i <= j < a.len()
    ensures sum(a, i, j + 1) == sum(a, i, j) + a[j]
    decreases j - i
{
    if i == j {
        // When i == j, sum(a, i, j) == 0 by definition
        assert(sum(a, i, j) == 0);
        // sum(a, i, j + 1) == sum(a, i, i + 1) == a[i] + sum(a, i + 1, i + 1) == a[i] + 0 == a[i]
        assert(sum(a, i, j + 1) == a[i] + sum(a, i + 1, j + 1));
        assert(sum(a, i + 1, j + 1) == 0);  // since i + 1 >= j + 1
        assert(sum(a, i, j + 1) == a[i]);
        // Since i == j, a[j] == a[i]
        assert(a[j] == a[i]);
        // Therefore sum(a, i, j + 1) == a[i] == a[j] == sum(a, i, j) + a[j]
        assert(sum(a, i, j + 1) == sum(a, i, j) + a[j]);
    } else {
        // Recursive case: i < j
        assert(sum(a, i, j + 1) == a[i] + sum(a, i + 1, j + 1));
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        
        // Apply inductive hypothesis
        lemma_sum_extend(a, i + 1, j);
        assert(sum(a, i + 1, j + 1) == sum(a, i + 1, j) + a[j]);
        
        // Combine the results
        assert(sum(a, i, j + 1) == a[i] + sum(a, i + 1, j + 1));
        assert(sum(a, i, j + 1) == a[i] + (sum(a, i + 1, j) + a[j]));
        assert(sum(a, i, j + 1) == (a[i] + sum(a, i + 1, j)) + a[j]);
        assert(sum(a, i, j + 1) == sum(a, i, j) + a[j]);
    }
}

fn query(a: Vec<int>, i: int, j: int) -> (s: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        s == sum(a, i, j)
{
    let mut total = 0;
    let mut idx = i;
    
    while idx < j
        invariant
            i <= idx <= j,
            total == sum(a, i, idx)
        decreases j - idx
    {
        // Before accessing a[idx], we need to ensure idx is within bounds
        // From loop condition: idx < j
        // From precondition: j <= a.len()
        // Therefore: idx < a.len()
        
        // We want to show: total + a[idx] == sum(a, i, idx + 1)
        // We know: total == sum(a, i, idx) from invariant
        // We need: sum(a, i, idx + 1) == sum(a, i, idx) + a[idx]
        
        // To use lemma_sum_extend, we need: 0 <= i <= idx < a.len()
        // We have: i <= idx from invariant, idx < j from loop condition, j <= a.len() from precondition
        // So: i <= idx < j <= a.len(), which gives us i <= idx < a.len()
        
        lemma_sum_extend(a, i, idx);
        
        total = total + a[idx];
        idx = idx + 1;
    }
    
    total
}

}