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
/* helper modified by LLM (iteration 5): lemma to relate recursive sum step */
spec fn sum_step(a: Seq<int>, s: int, t: int) -> bool {
    if 0 <= s <= t && t + 1 <= a.len() {
        sum(a, s, t + 1) == sum(a, s, t) + a@[t]
    } else {
        true
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
  /* code modified by LLM (iteration 5): compute minimal subarray sum using ghost seq and ghost mutable accumulators */
  let n: usize = a.len();
  if n == 0 {
    return 0i8;
  }

  let ghost seq: Seq<int> = a@.map(|_, x| x as int);

  let ghost mut best_sum: int = 0;
  let ghost mut best_k: int = 0;
  let ghost mut best_m: int = 0;

  let mut s_idx: usize = 0;
  while s_idx < n
      invariant
          s_idx <= n,
          forall|p: int, q: int| 0 <= p <= q <= n as int && (p < s_idx as int) ==> sum(seq, p, q) >= best_sum,
      decreases n - s_idx
  {
      let mut e: usize = s_idx;
      let ghost mut cur_sum: int = 0;

      while e <= n
          invariant
              s_idx <= e && e <= n,
              cur_sum == sum(seq, s_idx as int, e as int),
              forall|p: int, q: int| 0 <= p <= q <= n as int && (p < s_idx as int || (p == s_idx as int && q <= e as int)) ==> sum(seq, p, q) >= best_sum,
          decreases n - e
      {
          if cur_sum < best_sum {
              proof {
                  best_sum = cur_sum;
                  best_k = s_idx as int;
                  best_m = e as int;
              }
          }

          if e == n {
              break;
          } else {
              let old_e = e;
              proof {
                  assert(sum_step(seq, s_idx as int, old_e as int));
              }
              cur_sum = cur_sum + seq@[e];
              e = e + 1;
          }
      }

      s_idx = s_idx + 1;
  }

  proof {
      assert(0 <= best_k && best_k <= best_m && best_m <= n as int);
      assert(best_sum == sum(seq, best_k, best_m));
      assert(forall|p: int, q: int| 0 <= p <= q <= n as int ==> sum(seq, p, q) >= best_sum);
  }

  let ret: i8 = best_sum as i8;
  ret
}

// </vc-code>


}

fn main() {}