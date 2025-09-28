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
/* helper modified by LLM (iteration 5): The `compute_b_for_loop` helper was not used anywhere. Removing it. */
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
{
    let n_int: int = n as int;
    let a_seq: Seq<int> = a@.map(|i, x: i8| x as int);

    let mut min_cc_val: int = compute_cc(n_int, a_seq, 0);
    let mut optimal_idx_val: int = 0;

    let mut i: int = 1;
    while i < n_int
        invariant
            0 <= i <= n_int,
            optimal_idx_val < i,
            min_cc_val == compute_cc(n_int, a_seq, optimal_idx_val),
            forall|k: int| 0 <= k < i ==> #[trigger] compute_cc(n_int, a_seq, k) >= min_cc_val,
            forall|k: int| 0 <= k < i ==> (compute_cc(n_int, a_seq, k) == min_cc_val ==> k >= optimal_idx_val),
        decreases n_int - i
    {
        let current_cc = compute_cc(n_int, a_seq, i);
        if current_cc < min_cc_val {
            min_cc_val = current_cc;
            optimal_idx_val = i;
        }
        // if current_cc == min_cc_val, optimal_idx_val already holds the smallest index
        i = i + 1;
    }
    (optimal_idx_val + 1) as i8
}
// </vc-code>


}

fn main() {}