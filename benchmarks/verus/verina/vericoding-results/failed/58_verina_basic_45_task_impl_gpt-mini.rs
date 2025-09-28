// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_product_precond(lst: Seq<i32>) -> bool {
    lst.len() > 1 &&
    (exists|x: i32| lst.contains(x) && is_even(x)) &&
    (exists|x: i32| lst.contains(x) && is_odd(x))
}

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}

spec fn first_even_odd_indices(lst: Seq<i32>) -> Option<(int, int)> {
    let even_index = (choose|i: int| 0 <= i < lst.len() && is_even(lst[i]));
    let odd_index = (choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]));
    if (exists|i: int| 0 <= i < lst.len() && is_even(lst[i])) &&
       (exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])) {
        Some((even_index, odd_index))
    } else {
        None
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide spec witnesses that return chosen even/odd indices */
spec fn witnesses_even_odd(lst: Seq<i32>) -> (int, int) {
    let ei = (choose|i: int| 0 <= i < lst.len() && is_even(lst[i]));
    let oi = (choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]));
    (ei, oi)
}
// </vc-helpers>

// <vc-spec>
fn find_product(lst: &Vec<i32>) -> (result: i32)
    requires 
        lst.len() > 1,
        exists|x: i32| lst@.contains(x) && is_even(x),
        exists|x: i32| lst@.contains(x) && is_odd(x),
    ensures
        match first_even_odd_indices(lst@) {
            Some((ei, oi)) => result == lst@[ei] * lst@[oi],
            None => true,
        }
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): scan vector to find first even and odd elements and return their product */
  let mut ei: Option<usize> = None;
  let mut oi: Option<usize> = None;
  for i in 0..lst.len() {
    let val = lst[i];
    if ei.is_none() && val % 2 == 0 {
      ei = Some(i);
    }
    if oi.is_none() && val % 2 != 0 {
      oi = Some(i);
    }
    if ei.is_some() && oi.is_some() {
      break;
    }
  }
  let e = match ei {
    Some(idx) => idx,
    None => unreached(),
  };
  let o = match oi {
    Some(idx) => idx,
    None => unreached(),
  };
  lst[e] * lst[o]
}
// </vc-code>

}
fn main() {}