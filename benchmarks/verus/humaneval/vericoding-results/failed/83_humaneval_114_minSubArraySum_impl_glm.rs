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
spec fn iterative_sum_rec(a: Seq<int>, p: int, q: int) -> int
{
    if p >= q {
        0
    } else {
        a[p] + iterative_sum_rec(a, p + 1, q)
    }
}

proof fn lemma_sum_split(a: Seq<int>, p: int, q: int)
    requires 0 <= p < q <= a.len()
    ensures sum(a, p, q) == a[p] + sum(a, p + 1, q)
{
    if q - p == 1 {
        assert(sum(a, p, q) == a[p]);
    } else {
        lemma_sum_split(a, p, q - 1);
        assert(sum(a, p, q) == sum(a, p, q - 1) + a[q - 1]);
        assert(sum(a, p, q - 1) == a[p] + sum(a, p + 1, q - 1));
        assert(sum(a, p + 1, q) == sum(a, p + 1, q - 1) + a[q - 1]);
    }
}

proof fn lemma_iterative_sum_rec_eq_recursive_sum(a: Seq<int>, p: int, q: int)
    requires 0 <= p <= q <= a.len()
    ensures iterative_sum_rec(a, p, q) == sum(a, p, q)
{
    if p == q {
    } else {
        lemma_sum_split(a, p, q);
        lemma_iterative_sum_rec_eq_recursive_sum(a, p + 1, q);
    }
}
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<i8>) -> (s: i8)
  ensures forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= s as int &&
          (exists|k: int, m: int| #[trigger] sum(a@.map(|i, x| x as int), k, m) && 0 <= k <= m <= a@.len() && s as int == sum(a@.map(|i, x| x as int), k, m))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix min_sum initialization and overflow handling */
{
    let mut min_sum: i64 = 0;
    for p in 0..a.len() + 1 {
        for q in p..a.len() + 1 {
            let mut s: i64 = 0;
            for i in p..q {
                s += a[i] as i64;
            }
            if p == 0 && q == 0 {
                min_sum = s;
            } else if s < min_sum {
                min_sum = s;
            }
        }
    }
    min_sum as i8
}
// </vc-code>


}

fn main() {}