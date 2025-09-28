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
/* helper modified by LLM (iteration 5): fix ghost variable usage for digits_sum calls */
fn is_sorted_by_points(v: &Vec<i8>) -> (result: bool)
    ensures
        result == (forall|i: int, j: int| 0 <= i < j < v@.len() ==> digits_sum(v@[i] as int) <= digits_sum(v@[j] as int))
{
    for k in 0..v.len()
        invariant
            forall|i: int, j: int| 0 <= i < j < k ==> digits_sum(v@[i] as int) <= digits_sum(v@[j] as int)
    {
        for l in (k + 1)..v.len()
            invariant
                forall|i: int, j: int| 0 <= i < j < k ==> digits_sum(v@[i] as int) <= digits_sum(v@[j] as int),
                forall|j: int| (k as int) < j < l ==> digits_sum(v@[k as int] as int) <= digits_sum(v@[j] as int)
        {
            proof {
                let k_sum = digits_sum(v@[k as int] as int);
                let l_sum = digits_sum(v@[l as int] as int);
                if k_sum > l_sum {
                    return false;
                }
            }
        }
    }
    true
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
    /* code modified by LLM (iteration 5): fix index type errors from usize to int */
    let mut result = s.clone();
    let n = result.len();
    
    for i in 0..n
        invariant
            result@.len() == s@.len(),
            s@.to_multiset() == result@.to_multiset(),
            forall|p: int, q: int| 0 <= p < q < i ==> digits_sum(result@[p] as int) <= digits_sum(result@[q] as int)
    {
        for j in (i + 1)..n
            invariant
                result@.len() == s@.len(),
                s@.to_multiset() == result@.to_multiset(),
                forall|p: int, q: int| 0 <= p < q < i ==> digits_sum(result@[p] as int) <= digits_sum(result@[q] as int),
                forall|k: int| (i as int) < k < j ==> digits_sum(result@[i as int] as int) <= digits_sum(result@[k] as int)
        {
            let i_sum = digits_sum(result@[i as int] as int);
            let j_sum = digits_sum(result@[j as int] as int);
            if i_sum > j_sum {
                let temp = result[i as int];
                result.set(i as int, result[j as int]);
                result.set(j as int, temp);
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}