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
/* helper modified by LLM (iteration 4): predicate for verifying subarray sum */
spec fn subarray_sum_is(a: Seq<int>, k: int, m: int, s: int) -> bool
{
  0 <= k && k <= m && m <= a.len() && sum(a, k, m) == s
}
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<i8>) -> (s: i8)
  ensures forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@.map(|i, x| x as int), p, q) >= s as int &&
          (exists|k: int, m: int| #[trigger] sum(a@.map(|i, x| x as int), k, m) && 0 <= k <= m <= a@.len() && s as int == sum(a@.map(|i, x| x as int), k, m))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use i32 for executable calculations to avoid type errors */
{
  let n: usize = a.len();
  let mut min_val: i32 = if n > 0 { a[0] as i32 } else { 0 };
  let mut current_min: i32 = if n > 0 { a[0] as i32 } else { 0 };
  let mut i: usize = 1;
  while i < n
    invariant
      1 <= i <= n,
      true,
    decreases n - i
  {
    let mut new_current: i32 = current_min + a[i] as i32;
    if new_current >= a[i] as i32 {
      new_current = a[i] as i32;
    }
    current_min = new_current;
    if current_min < min_val {
      min_val = current_min;
    }
    i = i + 1;
  }
  if min_val > 0 {
    min_val = 0;
  }
  min_val as i8
}
// </vc-code>


}

fn main() {}