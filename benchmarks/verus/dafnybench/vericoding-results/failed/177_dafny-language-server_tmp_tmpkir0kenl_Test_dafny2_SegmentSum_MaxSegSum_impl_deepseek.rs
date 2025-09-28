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
spec fn update_max(r: (int, int), a: Seq<int>, val: int) -> (int, int) {
    if val > sum(a, r.0 as int, r.1 as int) {
        (r.0, r.1)
    } else {
        r
    }
}

proof fn lemma_sum_empty(a: Seq<int>, s: int)
    requires 0 <= s <= a.len()
    ensures sum(a, s, s) == 0
{}

proof fn lemma_sum_append(a: Seq<int>, s: int, t: int)
    requires 0 <= s < t <= a.len()
    ensures sum(a, s, t) == sum(a, s, t-1) + a[t-1]
{}

proof fn lemma_sum_monotonic(a: Seq<int>, s: int, t: int, u: int)
    requires 0 <= s <= t <= u <= a.len()
    ensures sum(a, s, t) <= sum(a, s, u)
    decreases u - t
{
    if t < u {
        lemma_sum_append(a, s, u);
        lemma_sum_monotonic(a, s, t, u-1);
    }
}

proof fn lemma_sum_triangle(a: Seq<int>, s: int, t: int, u: int)
    requires 0 <= s <= t <= u <= a.len()
    ensures sum(a, s, u) == sum(a, s, t) + sum(a, t, u)
    decreases u - t
{
    if t < u {
        lemma_sum_append(a, s, u);
        lemma_sum_triangle(a, s, t, u-1);
        lemma_sum_append(a, t, u);
    } else {
        lemma_sum_empty(a, t);
    }
}

proof fn lemma_sum_non_negative(a: Seq<int>, s: int, t: int, u: int)
    requires 0 <= s <= t <= u <= a.len()
    ensures sum(a, t, u) <= sum(a, s, u)
    decreases u - t
{
    if t < u {
        lemma_sum_append(a, t, u);
        lemma_sum_append(a, s, u);
        lemma_sum_non_negative(a, s, t+1, u);
    }
}

proof fn lemma_sum_shift(a: Seq<int>, s: int, t: int)
    requires 0 <= s < t <= a.len()
    ensures sum(a, s+1, t) == sum(a, s, t) - a[s]
{
    lemma_sum_triangle(a, s, s+1, t);
    lemma_sum_empty(a, s);
}

proof fn lemma_cast_usize_int(n: usize)
    ensures n as int >= 0
{}
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
    let mut max_sum: int = 0;
    let mut max_range: (usize, usize) = (0, 0);
    let mut current_sum: int = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    
    while right < n
        invariant
            0 <= left <= right <= n,
            current_sum == sum(a@, left as int, right as int),
            max_sum == sum(a@, max_range.0 as int, max_range.1 as int),
            forall |p: int, q: int| 0 <= p <= q <= right as int ==> sum(a@, p, q) <= max_sum,
            max_range.0 <= max_range.1 <= n
        decreases n - right
    {
        proof { lemma_cast_usize_int(right); }
        current_sum = current_sum + a[right] as int;
        right = right + 1;
        
        proof {
            lemma_cast_usize_int(left);
            lemma_cast_usize_int(right);
            lemma_sum_append(a@, left as int, right as int);
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            max_range = (left, right);
        }
        
        while current_sum < 0 && left < right
            invariant
                0 <= left <= right <= n,
                current_sum == sum(a@, left as int, right as int),
                max_sum == sum(a@, max_range.0 as int, max_range.1 as int),
                forall |p: int, q: int| 0 <= p <= q <= right as int ==> sum(a@, p, q) <= max_sum,
                max_range.0 <= max_range.1 <= n
            decreases right - left
        {
            proof { lemma_cast_usize_int(left); }
            proof {
                lemma_cast_usize_int(left);
                lemma_cast_usize_int(right);
                lemma_sum_shift(a@, left as int, right as int);
            }
            current_sum = current_sum - a[left] as int;
            left = left + 1;
        }
    }
    
    max_range
}
// </vc-code>

fn main() {}

}