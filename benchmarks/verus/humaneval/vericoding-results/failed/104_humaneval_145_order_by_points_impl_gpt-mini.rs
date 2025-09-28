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
fn find_min_index(v: &Vec<i8>) -> int
    requires
        v@.len() > 0,
    ensures
        0 <= result < v@.len(),
        forall|j: int| 0 <= j < v@.len() ==> digits_sum(v@[result] as int) <= digits_sum(v@[j] as int),
{
    let mut idx: int = 0;
    let mut i: int = 1;
    while i < v@.len()
        invariant
            0 <= idx < v@.len(),
            0 <= i <= v@.len(),
            forall|j: int| 0 <= j < i ==> digits_sum(v@[idx] as int) <= digits_sum(v@[j] as int),
        decreases v@.len() - i
    {
        if digits_sum(v@[i] as int) < digits_sum(v@[idx] as int) {
            idx = i;
        }
        i = i + 1;
    }
    idx
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
    let mut cur: Vec<i8> = s.clone();
    let mut res: Vec<i8> = Vec::new();
    while cur@.len() > 0
        invariant
            res@.len() + cur@.len() == s@.len(),
            s@.to_multiset() == res@.to_multiset() + cur@.to_multiset(),
            forall|i: int, j: int| 0 <= i < j < res@.len() ==> digits_sum(res@[i] as int) <= digits_sum(res@[j] as int),
            forall|i: int, j: int| 0 <= i < res@.len() && 0 <= j < cur@.len() ==> digits_sum(res@[i] as int) <= digits_sum(cur@[j] as int),
        decreases cur@.len()
    {
        let mi = find_min_index(&cur);
        let x = cur.remove(mi);
        res.push(x);
    }
    res
}
// </vc-code>


}

fn main() {}