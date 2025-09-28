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
/* helper modified by LLM (iteration 5): No helpers added, maps fixed in code */

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
/* code modified by LLM (iteration 5): Fixed compilation error by replacing ignored pattern with bound variable in map */
{
    let mut best_i: usize = 0;
    let b: i64 = (a[0] as i64);
    let c: i64 = if b < 0 { b / (n as i64) } else { (b + (n as i64) - 1) / (n as i64) };
    let mut best_val: i64 = (n as i64) * c;
    let mut j: usize = 1;
    while j < (n as usize)
        invariant
            valid_input(n as int, a@.map(|s, x: i8| x as int)),
            0 <= (best_i as int) < (n as int),
            (j as int) <= (n as int),
            forall |k: int| 0 <= k < (j as int) ==> {
              let bk = a@.map(|t, x: i8| x as int)[k] - k;
              let ck = if bk < 0 { bk / (n as int) } else { (bk + (n as int) - 1) / (n as int) };
              let cc_k = (n as int) * ck;
              let bb = a@.map(|u, x: i8| x as int)[best_i as int] - (best_i as int);
              let bc = if bb < 0 { bb / (n as int) } else { (bb + (n as int) - 1) / (n as int) };
              let cc_best = (n as int) * bc;
              cc_best <= cc_k && (cc_best < cc_k || (best_i as int) <= k)
            },
            (best_val as int) == {
              let bb = a@.map(|v, x: i8| x as int)[best_i as int] - (best_i as int);
              let bc = if bb < 0 { bb / (n as int) } else { (bb + (n as int) - 1) / (n as int) };
              (n as int) * bc
            },
        decreases (n as int) - (j as int)
    {
        let b: i64 = (a[j] as i64) - (j as i64);
        let c: i64 = if b < 0 { b / (n as i64) } else { (b + (n as i64) - 1) / (n as i64) };
        let val: i64 = (n as i64) * c;
        if val < best_val || (val == best_val && j < best_i) {
            best_i = j;
            best_val = val;
        }
        j = j + 1;
    }
    proof {
        assert(is_optimal_entrance(n as int, a@.map(|w, x: i8| x as int), (best_i + 1) as int));
    }
    (best_i + 1) as i8
}

// </vc-code>


}

fn main() {}