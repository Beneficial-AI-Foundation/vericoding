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

proof fn compute_cc_lemma(n: int, a: Seq<int>, i: int, j: int)
    requires
        valid_input(n, a),
        0 <= i < n,
        0 <= j < n,
    ensures
        compute_cc(n, a, i) <= compute_cc(n, a, j) || compute_cc(n, a, j) <= compute_cc(n, a, i),
{
    let bi = compute_b(a, i);
    let bj = compute_b(a, j);
    let ci = compute_c(n, bi);
    let cj = compute_c(n, bj);
    assert(ci <= cj || cj <= ci);
    assert(n * ci <= n * cj || n * cj <= n * ci);
}

proof fn tie_break_lemma(n: int, a: Seq<int>, i: int, j: int)
    requires
        valid_input(n, a),
        0 <= i < n,
        0 <= j < n,
        compute_cc(n, a, i) == compute_cc(n, a, j),
    ensures
        i <= j || j <= i,
{
    let bi = compute_b(a, i);
    let bj = compute_b(a, j);
    let ci = compute_c(n, bi);
    let cj = compute_c(n, bj);
    assert(compute_cc(n, a, i) == n * ci);
    assert(compute_cc(n, a, j) == n * cj);
    assert(ci == cj);
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
    /* code modified by LLM (iteration 5): Fixed syntax error by adding semicolon */
    let mut best_entrance = 0;
    let mut best_cc: int = 0;
    
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n as usize,
            best_entrance >= 0,
            if i > 0 {
                best_entrance < n as usize,
                0 <= best_entrance < n as usize,
                is_optimal_entrance(n as int, a@.map(|i, x: i8| x as int), (best_entrance + 1) as int) || i == 0
            } else { true }
        decreases (n as int - i as int),
    {
        let current_cc = compute_cc(n as int, a@.map(|i, x: i8| x as int), i as int);
        
        if i == 0 {
            best_entrance = i;
            best_cc = current_cc;
        } else {
            let best_cc_val = compute_cc(n as int, a@.map(|i, x: i8| x as int), best_entrance as int);
            
            if current_cc < best_cc_val {
                best_entrance = i;
                best_cc = current_cc;
            } else if current_cc == best_cc_val && i < best_entrance {
                best_entrance = i;
                best_cc = current_cc;
            }
        }
        
        i = i + 1;
    }
    
    (best_entrance + 1) as i8
}
// </vc-code>


}

fn main() {}