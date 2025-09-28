// RUN: %verus "%s"

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
    decreases t - s when 0 <= s <= t <= a.len()
{
    if s == t { 0 } else { sum(a, s, t-1) + a[t-1] }
}

// <vc-helpers>
proof fn lemma_sum_empty(a: Seq<int>, s: int)
    requires 0 <= s <= a.len()
    ensures sum(a, s, s) == 0
{
}

proof fn lemma_sum_extend(a: Seq<int>, s: int, t: int)
    requires 0 <= s <= t < a.len()
    ensures sum(a, s, t+1) == sum(a, s, t) + a[t]
{
}

proof fn lemma_sum_single(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures sum(a, i, i+1) == a[i]
{
}

proof fn lemma_sum_monotonic(a: Seq<int>, s: int, t1: int, t2: int)
    requires 0 <= s <= t1 <= t2 <= a.len()
    ensures sum(a, s, t2) == sum(a, s, t1) + sum(a, t1, t2)
    decreases t2 - t1
{
    if t1 == t2 {
        lemma_sum_empty(a, t1);
    } else {
        lemma_sum_monotonic(a, s, t1, t2-1);
        lemma_sum_extend(a, s, t2-1);
        lemma_sum_extend(a, t1, t2-1);
    }
}
// </vc-helpers>

// <vc-spec>
fn max_seg_sum(a: &Vec<int>) -> (result: (usize, usize))
    ensures ({
        let (k, m) = result;
        &&& k <= m <= a.len()
        &&& forall |p: int, q: int| 0 <= p <= q <= a.len() ==> 
            sum(a@, p, q) <= sum(a@, k as int, m as int)
    })
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        return (0, 0);
    }
    
    let mut max_sum = sum(a@, 0, 0);
    let mut max_start = 0usize;
    let mut max_end = 0usize;
    
    let mut i = 0usize;
    while i <= a.len()
        invariant 
            0 <= i <= a.len(),
            max_start <= max_end <= a.len(),
            forall |p: int, q: int| 0 <= p <= q <= i ==> 
                sum(a@, p, q) <= sum(a@, max_start as int, max_end as int),
            max_sum == sum(a@, max_start as int, max_end as int)
    {
        let mut j = i;
        while j <= a.len()
            invariant 
                i <= j <= a.len(),
                max_start <= max_end <= a.len(),
                forall |p: int, q: int| 
                    (0 <= p <= q <= i || (i <= p <= q <= j && p == i)) ==> 
                    sum(a@, p, q) <= sum(a@, max_start as int, max_end as int),
                max_sum == sum(a@, max_start as int, max_end as int)
        {
            let current_sum = sum(a@, i as int, j as int);
            if current_sum > max_sum {
                max_sum = current_sum;
                max_start = i;
                max_end = j;
            }
            
            assert(forall |p: int, q: int| 
                (0 <= p <= q <= i || (i <= p <= q <= j+1 && p == i)) ==> 
                sum(a@, p, q) <= sum(a@, max_start as int, max_end as int));
            
            j += 1;
        }
        
        assert(forall |p: int, q: int| 
            (0 <= p <= q <= i || (i <= p <= q <= a.len() && p == i)) ==> 
            sum(a@, p, q) <= sum(a@, max_start as int, max_end as int));
        
        i += 1;
    }
    
    (max_start, max_end)
}
// </vc-code>

fn main() {}

}