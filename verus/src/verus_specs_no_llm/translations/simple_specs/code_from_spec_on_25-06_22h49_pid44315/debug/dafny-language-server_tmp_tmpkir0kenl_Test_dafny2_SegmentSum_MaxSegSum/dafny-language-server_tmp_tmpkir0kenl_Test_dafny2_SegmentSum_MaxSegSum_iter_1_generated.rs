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
            forall p,q :: 0 <= p <= q <= a.len() && q <= i ==> Sum(a, p, q) <= best_sum,
            best_sum == Sum(a, best_k, best_m)
    {
        let mut j = i;
        let mut current_sum = 0;
        
        while j < a.len()
            invariant
                i <= j <= a.len(),
                0 <= best_k <= best_m <= a.len(),
                forall p,q :: 0 <= p <= q <= a.len() && (q < i || (p == i && q <= j)) ==> Sum(a, p, q) <= best_sum,
                best_sum == Sum(a, best_k, best_m),
                current_sum == Sum(a, i, j)
        {
            current_sum = current_sum + a[j];
            
            assert(Sum(a, i, j + 1) == current_sum) by {
                lemma_sum_extend(a, i, j + 1);
            }
            
            if current_sum > best_sum {
                best_k = i;
                best_m = j + 1;
                best_sum = current_sum;
            }
            
            j = j + 1;
        }
        
        i = i + 1;
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

}

The implementation:


   - Outer loop iterates through all possible starting positions
   - Inner loop extends from each starting position to find the best ending position
   - Maintains the best found subarray bounds and sum



The algorithm ensures we find the truly optimal subarray by exhaustively checking all possibilities while maintaining the required invariants for verification.