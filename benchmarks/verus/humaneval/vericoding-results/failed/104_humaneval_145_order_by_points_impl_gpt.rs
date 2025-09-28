// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digits_sum_pos(n: int) -> int
  decreases n
{
  if n >= 0 {
    if n < 10 { n } else { digits_sum_pos(n / 10) + n % 10 }
  } else {
    0
  }
}

spec fn digits_sum(n: int) -> int {
  if n < 0 { digits_sum_pos(-n) } else { digits_sum_pos(n) }
}
// </vc-preamble>

// <vc-helpers>
spec fn weight(x: i8) -> int {
    digits_sum(x as int)
}
// </vc-helpers>

// <vc-spec>
fn order_by_points(s: Vec<i8>) -> (sorted: Vec<i8>)
  ensures 
      forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> digits_sum(sorted@[i] as int) <= digits_sum(sorted@[j] as int),
      sorted@.len() == s@.len(),
      s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut v = s.clone();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i as int <= v@.len(),
            forall|p: int, q: int| 0 <= p < q < i as int ==> digits_sum(v@[p] as int) <= digits_sum(v@[q] as int),
            forall|p: int, q: int| 0 <= p < i as int <= q < v@.len() ==> digits_sum(v@[p] as int) <= digits_sum(v@[q] as int),
            v@.len() == s@.len(),
            v@.to_multiset() == s@.to_multiset(),
        decreases v@.len() - i as int
    {
        let mut min_j: usize = i;
        let mut j: usize = i + 1;
        while j < v.len()
            invariant
                i as int <= min_j as int,
                min_j < j,
                j as int <= v@.len(),
                forall|k: int| i as int <= k < j as int ==> digits_sum(v@[min_j as int] as int) <= digits_sum(v@[k] as int),
            decreases v@.len() - j as int
        {
            let wj = digits_sum(v@[j as int] as int);
            let wmin = digits_sum(v@[min_j as int] as int);
            if wj < wmin {
                min_j = j;
            }
            j = j + 1;
        }
        let _oldv = v@;
        v.swap(i, min_j);
        i = i + 1;
    }
    v
}
// </vc-code>


}

fn main() {}