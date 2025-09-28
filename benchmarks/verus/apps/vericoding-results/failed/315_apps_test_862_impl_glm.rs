// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
  n >= 2 && a.len() == n && (forall|i: int| 0 <= i < n ==> #[trigger] a[i] >= 0)
}

spec fn compute_b(a: Seq<int>, i: int) -> int
  recommends 0 <= i < a.len()
{
  a[i] - i
}

spec fn compute_c(n: int, b: int) -> int
  recommends n >= 2
{
  if b < 0 { b / n } else { (b + n - 1) / n }
}

spec fn compute_cc(n: int, a: Seq<int>, i: int) -> int
  recommends valid_input(n, a) && 0 <= i < n
{
  let b = compute_b(a, i);
  let c = compute_c(n, b);
  n * c
}

spec fn is_optimal_entrance(n: int, a: Seq<int>, entrance: int) -> bool
  recommends valid_input(n, a) && 1 <= entrance <= n
{
  let i = entrance - 1;
  forall|j: int| 0 <= j < n ==> {
    let cci = compute_cc(n, a, i);
    let ccj = #[trigger] compute_cc(n, a, j);
    cci <= ccj && (cci < ccj || i <= j)
  }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
  requires
    valid_input(n as int, a@.map(|i, x: i8| x as int)),
  ensures
    1 <= result as int <= n as int,
    is_optimal_entrance(n as int, a@.map(|i, x: i8| x as int), result as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): moved mapped_seq definition to top, changed min_cc and cc_i to int, fixed loop invariant */
{
    let mapped_seq = a@.map(|i, x| x as int);
    let mut min_index: int = 0;
    let mut min_cc: int = compute_cc(n as int, mapped_seq, 0);
    let mut i: int = 1;
    while i < n as int
        invariant 
            1 <= i <= n as int,
            0 <= min_index < i,
            min_cc == compute_cc(n as int, mapped_seq, min_index),
            forall|j: int| 0 <= j < i ==> min_cc <= #[trigger] compute_cc(n as int, mapped_seq, j),
            forall|j: int| 0 <= j < min_index ==> #[trigger] compute_cc(n as int, mapped_seq, j) > min_cc
        decreases (n as int) - i
    {
        let cc_i: int = compute_cc(n as int, mapped_seq, i);
        if cc_i < min_cc {
            min_cc = cc_i;
            min_index = i;
        }
        i = i + 1;
    }
    (min_index + 1) as i8
}
// </vc-code>


}

fn main() {}