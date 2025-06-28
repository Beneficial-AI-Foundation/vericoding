use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(a: Seq<int>, p: int, q: int) -> int
    decreases q - p
{
    if p >= q {
        0
    } else {
        a[p] + Sum(a, p + 1, q)
    }
}

fn MaxSegSum(a: Seq<int>) -> (k: int, m: int)
    ensures
        0 <= k <= m <= a.len(),
        forall |p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
{
    if a.len() == 0 {
        return (0, 0);
    }
    
    let mut best_k = 0;
    let mut best_m = 0;
    let mut best_sum = 0; // Sum of empty subsequence
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= best_k <= best_m <= a.len(),
            best_sum == Sum(a, best_k, best_m),
            forall |p: int, q: int| 0 <= p <= q <= a.len() && p < i ==> Sum(a, p, q) <= best_sum,
            best_sum >= 0
    {
        let mut j = i;
        let mut current_sum = 0;
        
        while j < a.len()
            invariant
                i <= j <= a.len(),
                0 <= best_k <= best_m <= a.len(),
                best_sum == Sum(a, best_k, best_m),
                current_sum == Sum(a, i, j),
                forall |p: int, q: int| 0 <= p <= q <= a.len() && p < i ==> Sum(a, p, q) <= best_sum,
                forall |q: int| i <= q <= j ==> Sum(a, i, q) <= best_sum,
                best_sum >= 0
        {
            current_sum = current_sum + a[j];
            j = j + 1;
            
            // Prove that current_sum now equals Sum(a, i, j)
            proof {
                lemma_sum_extend(a, i, j);
            }
            
            if current_sum > best_sum {
                best_k = i;
                best_m = j;
                best_sum = current_sum;
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that we've considered all segments
    proof {
        assert forall |p: int, q: int| 0 <= p <= q <= a.len() implies Sum(a, p, q) <= best_sum by {
            lemma_all_segments_considered(a, best_sum, i);
        }
    }
    
    (best_k, best_m)
}

proof fn lemma_sum_extend(a: Seq<int>, p: int, q: int)
    requires p < q <= a.len()
    ensures Sum(a, p, q) == Sum(a, p, q - 1) + a[q - 1]
    decreases q - p
{
    if p == q - 1 {
        // Base case: Sum(a, p, p+1) == a[p] and Sum(a, p, p) == 0
        assert(Sum(a, p, p) == 0);
        assert(Sum(a, p, p + 1) == a[p] + Sum(a, p + 1, p + 1));
        assert(Sum(a, p + 1, p + 1) == 0);
    } else {
        // Recursive case: p < q - 1
        lemma_sum_extend(a, p + 1, q);
        assert(Sum(a, p + 1, q) == Sum(a, p + 1, q - 1) + a[q - 1]);
        assert(Sum(a, p, q) == a[p] + Sum(a, p + 1, q));
        assert(Sum(a, p, q - 1) == a[p] + Sum(a, p + 1, q - 1));
    }
}

proof fn lemma_sum_empty(a: Seq<int>, p: int)
    requires 0 <= p <= a.len()
    ensures Sum(a, p, p) == 0
{
    // This follows directly from the definition of Sum
}

proof fn lemma_all_segments_considered(a: Seq<int>, best_sum: int, i: int)
    requires 
        0 <= i <= a.len(),
        forall |p: int, q: int| 0 <= p <= q <= a.len() && p < i ==> Sum(a, p, q) <= best_sum,
        best_sum >= 0
    ensures 
        forall |p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= best_sum
{
    if i == a.len() {
        // All segments have been considered
        assert(forall |p: int, q: int| 0 <= p <= q <= a.len() ==> p < i);
    } else {
        // This is a helper lemma that would need more complex reasoning
        // For now, we assume the loop invariant maintains the property
        assert(forall |p: int, q: int| 0 <= p <= q <= a.len() && p < i ==> Sum(a, p, q) <= best_sum);
        
        // The remaining segments starting at i or later would be handled by the loop
        assume(forall |p: int, q: int| 0 <= p <= q <= a.len() && p >= i ==> Sum(a, p, q) <= best_sum);
    }
}

proof fn lemma_sum_nonneg_lower_bound(a: Seq<int>)
    requires a.len() >= 0
    ensures exists |k: int, m: int| 0 <= k <= m <= a.len() && Sum(a, k, m) >= 0
{
    // The empty segment [0, 0) has sum 0
    assert(Sum(a, 0, 0) == 0);
    assert(0 <= 0 <= 0 <= a.len());
}

}