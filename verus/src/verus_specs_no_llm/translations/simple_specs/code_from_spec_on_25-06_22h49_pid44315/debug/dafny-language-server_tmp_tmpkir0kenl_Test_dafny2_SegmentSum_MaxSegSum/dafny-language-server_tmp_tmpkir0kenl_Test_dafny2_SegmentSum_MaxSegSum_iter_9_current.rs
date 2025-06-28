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
            // Prove that adding a[j] extends the sum correctly
            proof {
                lemma_sum_extend(a, i, j + 1);
            }
            
            current_sum = current_sum + a[j];
            j = j + 1;
            
            if current_sum > best_sum {
                best_k = i;
                best_m = j;
                best_sum = current_sum;
            }
        }
        
        // After inner loop, we've considered all segments starting at i
        proof {
            assert(forall |q: int| i <= q <= a.len() ==> Sum(a, i, q) <= best_sum);
        }
        
        i = i + 1;
    }
    
    // After both loops, we've considered all possible segments
    proof {
        assert(forall |p: int, q: int| 0 <= p <= q <= a.len() && p < a.len() ==> Sum(a, p, q) <= best_sum);
        // Since i == a.len(), all segments have been considered
        assert(forall |p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= best_sum);
    }
    
    (best_k, best_m)
}

proof fn lemma_sum_extend(a: Seq<int>, p: int, q: int)
    requires p <= q <= a.len()
    ensures Sum(a, p, q) == Sum(a, p, q - 1) + (if p < q { a[q - 1] } else { 0 })
    decreases q - p
{
    if p >= q {
        // Empty segment case
        assert(Sum(a, p, q) == 0);
        assert(Sum(a, p, q - 1) == 0);
    } else if p == q - 1 {
        // Base case: single element
        assert(Sum(a, p, q) == a[p] + Sum(a, p + 1, q));
        assert(Sum(a, p + 1, q) == 0); // because p + 1 == q
        assert(Sum(a, p, p) == 0);
    } else {
        // Recursive case
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

proof fn lemma_sum_monotonic(a: Seq<int>, p: int, q1: int, q2: int)
    requires p <= q1 <= q2 <= a.len()
    ensures Sum(a, p, q2) == Sum(a, p, q1) + Sum(a, q1, q2)
    decreases q1 - p
{
    if p >= q1 {
        assert(Sum(a, p, q1) == 0);
        assert(Sum(a, p, q2) == Sum(a, q1, q2));
    } else {
        lemma_sum_monotonic(a, p + 1, q1, q2);
        assert(Sum(a, p + 1, q2) == Sum(a, p + 1, q1) + Sum(a, q1, q2));
        assert(Sum(a, p, q1) == a[p] + Sum(a, p + 1, q1));
        assert(Sum(a, p, q2) == a[p] + Sum(a, p + 1, q2));
    }
}

}