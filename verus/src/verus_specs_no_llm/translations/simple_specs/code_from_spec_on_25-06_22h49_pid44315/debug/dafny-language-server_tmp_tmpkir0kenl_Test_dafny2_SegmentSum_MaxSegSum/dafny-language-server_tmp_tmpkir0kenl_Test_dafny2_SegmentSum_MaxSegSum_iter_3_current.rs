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
        forall p,q :: 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
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
            forall p,q :: 0 <= p < i && p <= q <= a.len() ==> Sum(a, p, q) <= best_sum,
            forall p,q :: 0 <= p <= q <= a.len() && q <= i ==> Sum(a, p, q) <= best_sum
    {
        let mut j = i;
        let mut current_sum = 0;
        
        // Prove that current_sum equals Sum(a, i, j) initially
        assert(current_sum == Sum(a, i, j)) by {
            assert(Sum(a, i, i) == 0);
        }
        
        while j < a.len()
            invariant
                i <= j <= a.len(),
                0 <= best_k <= best_m <= a.len(),
                best_sum == Sum(a, best_k, best_m),
                current_sum == Sum(a, i, j),
                forall p,q :: 0 <= p < i && p <= q <= a.len() ==> Sum(a, p, q) <= best_sum,
                forall p,q :: 0 <= p <= q <= a.len() && q <= i ==> Sum(a, p, q) <= best_sum,
                forall q :: i <= q <= j ==> Sum(a, i, q) <= best_sum
        {
            current_sum = current_sum + a[j];
            j = j + 1;
            
            // Prove that current_sum now equals Sum(a, i, j)
            assert(current_sum == Sum(a, i, j)) by {
                lemma_sum_extend(a, i, j);
            }
            
            if current_sum > best_sum {
                best_k = i;
                best_m = j;
                best_sum = current_sum;
                
                // Prove the invariant is maintained after update
                assert(forall q :: i <= q <= j ==> Sum(a, i, q) <= best_sum) by {
                    lemma_sum_prefix_bound(a, i, j);
                }
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that all segments have been considered
    assert(forall p,q :: 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= best_sum) by {
        lemma_all_segments_covered(a, best_sum, a.len() as int);
    }
    
    (best_k, best_m)
}

proof fn lemma_sum_extend(a: Seq<int>, p: int, q: int)
    requires p < q <= a.len()
    ensures Sum(a, p, q) == Sum(a, p, q - 1) + a[q - 1]
    decreases q - p
{
    if p == q - 1 {
        assert(Sum(a, p, q - 1) == 0);
        assert(Sum(a, p, q) == a[p]);
    } else {
        lemma_sum_extend(a, p + 1, q);
        assert(Sum(a, p + 1, q) == Sum(a, p + 1, q - 1) + a[q - 1]);
        assert(Sum(a, p, q) == a[p] + Sum(a, p + 1, q));
        assert(Sum(a, p, q - 1) == a[p] + Sum(a, p + 1, q - 1));
    }
}

proof fn lemma_sum_prefix_bound(a: Seq<int>, p: int, q: int)
    requires p <= q <= a.len()
    ensures forall r :: p <= r <= q ==> Sum(a, p, r) <= Sum(a, p, q)
    decreases q - p
{
    if p >= q {
        return;
    }
    
    lemma_sum_prefix_bound(a, p, q - 1);
    
    let r = p;
    while r <= q
        invariant p <= r <= q + 1,
                 forall s :: p <= s < r ==> Sum(a, p, s) <= Sum(a, p, q)
    {
        if r < q {
            lemma_sum_extend(a, p, r + 1);
            lemma_sum_extend(a, p, q);
        }
        r = r + 1;
    }
}

proof fn lemma_all_segments_covered(a: Seq<int>, best_sum: int, n: int)
    requires n == a.len(),
             forall p,q :: 0 <= p < n && p <= q <= a.len() ==> Sum(a, p, q) <= best_sum,
             forall p,q :: 0 <= p <= q <= a.len() && q <= n ==> Sum(a, p, q) <= best_sum
    ensures forall p,q :: 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= best_sum
{
    // The preconditions already cover all possible segments
}

}