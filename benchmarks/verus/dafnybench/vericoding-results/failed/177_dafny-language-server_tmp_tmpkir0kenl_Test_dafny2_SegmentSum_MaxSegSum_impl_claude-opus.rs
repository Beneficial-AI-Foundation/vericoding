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
proof fn sum_empty(a: Seq<int>, s: int)
    requires 0 <= s <= a.len()
    ensures sum(a, s, s) == 0
{
    // Base case of sum definition
}

proof fn sum_single(a: Seq<int>, s: int)
    requires 0 <= s < a.len()
    ensures sum(a, s, s + 1) == a[s]
{
    assert(sum(a, s, s + 1) == sum(a, s, s) + a[s]);
    sum_empty(a, s);
}

proof fn sum_extend(a: Seq<int>, s: int, t: int)
    requires 0 <= s <= t < a.len()
    ensures sum(a, s, t + 1) == sum(a, s, t) + a[t]
{
    // By definition of sum
}

proof fn sum_split(a: Seq<int>, s: int, m: int, t: int)
    requires 0 <= s <= m <= t <= a.len()
    ensures sum(a, s, t) == sum(a, s, m) + sum(a, m, t)
    decreases t - m
{
    if m == t {
        sum_empty(a, m);
        assert(sum(a, m, t) == 0);
    } else {
        assert(sum(a, m, t) == sum(a, m, t - 1) + a[t - 1]);
        sum_split(a, s, m, t - 1);
        assert(sum(a, s, t - 1) == sum(a, s, m) + sum(a, m, t - 1));
        assert(sum(a, s, t) == sum(a, s, t - 1) + a[t - 1]);
        assert(sum(a, s, t) == sum(a, s, m) + sum(a, m, t - 1) + a[t - 1]);
        assert(sum(a, s, t) == sum(a, s, m) + sum(a, m, t));
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
    let n = a.len();
    if n == 0 {
        proof {
            assert forall |p: int, q: int| 0 <= p <= q <= 0 implies sum(a@, p, q) <= sum(a@, 0, 0) by {
                assert(p == 0 && q == 0);
                sum_empty(a@, 0);
            }
        }
        return (0, 0);
    }
    
    let mut max_k: usize = 0;
    let mut max_m: usize = 0;
    let mut max_sum: int = 0;
    
    proof {
        sum_empty(a@, 0);
    }
    
    let mut i: usize = 0;
    while i <= n
        invariant
            0 <= i <= n + 1,
            0 <= max_k <= max_m <= n,
            max_sum == sum(a@, max_k as int, max_m as int),
            forall |p: int, q: int| 0 <= p <= q <= i ==> 
                sum(a@, p, q) <= sum(a@, max_k as int, max_m as int),
    {
        let mut j: usize = i;
        let mut current_sum: int = 0;
        
        proof {
            sum_empty(a@, i as int);
        }
        
        while j <= n
            invariant
                i <= j <= n + 1,
                current_sum == sum(a@, i as int, j as int),
                0 <= max_k <= max_m <= n,
                max_sum == sum(a@, max_k as int, max_m as int),
                forall |p: int, q: int| 0 <= p <= q <= i ==>
                    sum(a@, p, q) <= sum(a@, max_k as int, max_m as int),
                forall |q: int| i <= q <= j ==>
                    sum(a@, i as int, q) <= sum(a@, max_k as int, max_m as int),
        {
            if current_sum > max_sum || (i == 0 && j == 0) {
                max_sum = current_sum;
                max_k = i;
                max_m = j;
            }
            
            if j < n {
                proof {
                    sum_extend(a@, i as int, j as int);
                }
                current_sum = current_sum + a[j];
                j = j + 1;
            } else {
                j = j + 1;
            }
        }
        
        i = i + 1;
    }
    
    (max_k, max_m)
}
// </vc-code>

fn main() {}

}