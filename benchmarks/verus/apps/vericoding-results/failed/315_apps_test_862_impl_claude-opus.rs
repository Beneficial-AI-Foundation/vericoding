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
/* helper modified by LLM (iteration 5): Added executable helper functions for i8 computations */
fn compute_b_exec(a: &Vec<i8>, i: i8) -> (result: i8)
    requires
        0 <= i < a.len(),
        a.len() <= i8::MAX,
    ensures
        result == compute_b(a@.map(|idx, x: i8| x as int), i as int),
{
    a[i as usize] - i
}

fn compute_c_exec(n: i8, b: i8) -> (result: i8)
    requires
        n >= 2,
    ensures
        result == compute_c(n as int, b as int),
{
    if b < 0 {
        b / n
    } else {
        (b + n - 1) / n
    }
}

fn compute_cc_exec(n: i8, a: &Vec<i8>, i: i8) -> (result: i8)
    requires
        valid_input(n as int, a@.map(|idx, x: i8| x as int)),
        0 <= i < n,
    ensures
        result == compute_cc(n as int, a@.map(|idx, x: i8| x as int), i as int),
{
    let b = compute_b_exec(a, i);
    let c = compute_c_exec(n, b);
    n * c
}
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
    /* code modified by LLM (iteration 5): Fixed syntax - added parentheses around forall body expression */
    let mut min_cc = compute_cc_exec(n, &a, 0);
    let mut min_index: i8 = 0;
    let mut i: i8 = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            0 <= min_index < i,
            min_cc == compute_cc(n as int, a@.map(|idx, x: i8| x as int), min_index as int),
            forall|j: int| 0 <= j < i as int ==> {
                let ccj = compute_cc(n as int, a@.map(|idx, x: i8| x as int), j);
                (min_cc as int <= ccj && (min_cc as int < ccj || min_index as int <= j))
            },
    {
        let cc_i = compute_cc_exec(n, &a, i);
        if cc_i < min_cc || (cc_i == min_cc && i < min_index) {
            min_cc = cc_i;
            min_index = i;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < n as int ==> {
            let ccj = compute_cc(n as int, a@.map(|idx, x: i8| x as int), j);
            min_cc as int <= ccj && (min_cc as int < ccj || min_index as int <= j)
        });
    }
    
    min_index + 1
}
// </vc-code>


}

fn main() {}