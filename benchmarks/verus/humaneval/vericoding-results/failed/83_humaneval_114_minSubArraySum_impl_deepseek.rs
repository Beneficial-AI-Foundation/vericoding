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
proof fn lemma_sum_nonnegative_if_nonnegative_elements(a: Seq<int>, s: int, t: int)
    requires
        0 <= s <= t <= a.len(),
        forall|i| 0 <= i < a.len() ==> a[i] >= 0,
    ensures sum(a, s, t) >= 0
decreases t - s
{
    if s < t {
        lemma_sum_nonnegative_if_nonnegative_elements(a, s, t - 1);
    }
}
/* helper modified by LLM (iteration 5): Added proof lemma for sums */
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<i8>) -> (s: i8)
  ensures forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= s as int &&
          (exists|k: int, m: int| #[trigger] sum(a@.map(|i, x| x as int), k, m) && 0 <= k <= m <= a@.len() && s as int == sum(a@.map(|i, x| x as int), k, m))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer casts in execution mode */
    let mut min_sum = 0;
    let mut i = 0;
    let a_len = a.len();
    let a_seq = a@;
    
    while i < a_len
        invariant
            min_sum <= 0,
            exists|k, m| 0 <= k <= m <= i && sum(a_seq.map(|i, x| x as int), k, m) == min_sum as int,
            forall|p, q| 0 <= p <= q <= i ==> sum(a_seq.map(|i, x| x as int), p, q) >= min_sum as int
        decreases a_len - i
    {
        let mut j = i;
        let mut current_sum = 0;
        let mut local_min = 0;
        
        while j < a_len
            invariant
                current_sum == sum(a_seq.map(|i, x| x as int), i, j),
                local_min <= 0,
                exists|m| i <= m <= j && sum(a_seq.map(|i, x| x as int), i, m) == local_min as int,
                forall|q| i <= q <= j ==> sum(a_seq.map(|i, x| x as int), i, q) >= local_min as int
            decreases a_len - j
        {
            current_sum = current_sum + (a[j] as i32) as i32;
            if current_sum < (local_min as i32) {
                local_min = current_sum as i8;
            }
            j = j + 1;
        }
        
        if local_min < min_sum {
            min_sum = local_min;
        }
        
        i = i + 1;
    }
    
    min_sum
}
// </vc-code>


}

fn main() {}