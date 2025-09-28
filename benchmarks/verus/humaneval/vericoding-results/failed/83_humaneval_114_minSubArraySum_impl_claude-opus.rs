// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
  decreases t - s
{
  if 0 <= s <= t <= a.len() {
    if s == t {
      0
    } else {
      sum(a, s, t - 1) + a[t - 1]
    }
  } else {
    0
  }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_empty(a: Seq<int>, s: int)
    requires
        0 <= s <= a.len(),
    ensures
        sum(a, s, s) == 0,
    decreases s,
{
    if s == 0 {
    } else {
        sum_empty(a, s - 1);
    }
}

proof fn sum_extend(a: Seq<int>, s: int, t: int)
    requires
        0 <= s < t <= a.len(),
    ensures
        sum(a, s, t) == sum(a, s, t - 1) + a[t - 1],
{
}

proof fn sum_split(a: Seq<int>, s: int, m: int, t: int)
    requires
        0 <= s <= m <= t <= a.len(),
    ensures
        sum(a, s, t) == sum(a, s, m) + sum(a, m, t),
    decreases t - m,
{
    if m == t {
        sum_empty(a, m);
    } else {
        sum_extend(a, m, t);
        sum_split(a, s, m, t - 1);
    }
}

proof fn sum_single(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum(a, i, i + 1) == a[i],
{
    sum_extend(a, i, i + 1);
    sum_empty(a, i);
}
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<i8>) -> (s: i8)
  ensures forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= s as int &&
          (exists|k: int, m: int| #[trigger] sum(a@.map(|i, x| x as int), k, m) && 0 <= k <= m <= a@.len() && s as int == sum(a@.map(|i, x| x as int), k, m))
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return 0;
    }
    
    let mut min_sum: i8 = 127;
    let mut min_k: usize = 0;
    let mut min_m: usize = 0;
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|p: int, q: int| 0 <= p <= q <= i ==> sum(a@.map(|idx, x| x as int), p, q) >= min_sum as int,
            0 <= min_k <= min_m <= n,
            min_sum as int == sum(a@.map(|idx, x| x as int), min_k as int, min_m as int),
    {
        let mut current_sum: i8 = 0;
        let mut j: usize = i;
        
        while j < n
            invariant
                i <= j <= n,
                current_sum as int == sum(a@.map(|idx, x| x as int), i as int, j as int),
                forall|p: int, q: int| 0 <= p <= q <= i ==> sum(a@.map(|idx, x| x as int), p, q) >= min_sum as int,
                0 <= min_k <= min_m <= n,
                min_sum as int == sum(a@.map(|idx, x| x as int), min_k as int, min_m as int),
                forall|q: int| i <= q < j ==> sum(a@.map(|idx, x| x as int), i as int, q + 1) >= min_sum as int,
        {
            current_sum = current_sum + a[j];
            j = j + 1;
            
            proof {
                assert(current_sum as int == sum(a@.map(|idx, x| x as int), i as int, j as int));
            }
            
            if current_sum < min_sum {
                min_sum = current_sum;
                min_k = i;
                min_m = j;
            }
        }
        
        i = i + 1;
    }
    
    min_sum
}
// </vc-code>


}

fn main() {}