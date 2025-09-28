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
/* helper modified by LLM (iteration 5): fixed trigger syntax by separating boolean conditions */
proof fn lemma_sum_properties(a: Seq<int>, s: int, t: int)
    ensures
        s == t ==> sum(a, s, t) == 0,
        s < t && 0 <= s < t <= a.len() ==> sum(a, s, t) == sum(a, s, t - 1) + a[t - 1],
        sum(a, s, s) == 0,
{
}

proof fn lemma_sum_bound(a: Seq<i8>, s: int, t: int, min_val: i8)
    requires
        0 <= s <= t <= a.len(),
        forall|i: int| s <= i < t ==> a[i] >= min_val,
    ensures
        sum(a.map(|i, x| x as int), s, t) >= (t - s) * (min_val as int),
{
    if s == t {
        assert(sum(a.map(|i, x| x as int), s, t) == 0);
    } else {
        lemma_sum_bound(a, s, t - 1, min_val);
        assert(a[t - 1] >= min_val);
        assert(sum(a.map(|i, x| x as int), s, t) == sum(a.map(|i, x| x as int), s, t - 1) + a[t - 1] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<i8>) -> (s: i8)
  ensures forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= s as int &&
          (exists|k: int, m: int| #[trigger] sum(a@.map(|i, x| x as int), k, m) && 0 <= k <= m <= a@.len() && s as int == sum(a@.map(|i, x| x as int), k, m))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed exists clause to use proper boolean condition */
    if a.len() == 0 {
        return 0;
    }
    
    let mut min_sum = a[0] as i8;
    let mut current_sum = a[0] as i8;
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int, m: int| 0 <= k <= m <= i && min_sum as int == sum(a@.map(|i, x| x as int), k, m),
            forall|p: int, q: int| 0 <= p <= q <= i ==> sum(a@.map(|i, x| x as int), p, q) >= min_sum as int,
    {
        if current_sum > 0 {
            current_sum = a[i];
        } else {
            current_sum = current_sum + a[i];
        }
        
        if current_sum < min_sum {
            min_sum = current_sum;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= min_sum as int);
        assert(exists|k: int, m: int| 0 <= k <= m <= a@.len() && min_sum as int == sum(a@.map(|i, x| x as int), k, m));
    }
    
    min_sum
}
// </vc-code>


}

fn main() {}