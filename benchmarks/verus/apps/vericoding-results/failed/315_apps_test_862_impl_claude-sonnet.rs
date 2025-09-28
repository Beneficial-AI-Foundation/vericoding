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
/* helper modified by LLM (iteration 5): Fixed compilation error by wrapping type conversions in proof blocks */
proof fn lemma_optimal_existence(n: int, a: Seq<int>)
    requires
        valid_input(n, a),
    ensures
        exists|entrance: int| 1 <= entrance <= n && is_optimal_entrance(n, a, entrance)
{
    let min_cc = seq_min(a.map(|i, x| compute_cc(n, a, i)));
    assert(exists|i: int| 0 <= i < n && compute_cc(n, a, i) == min_cc);
}

spec fn seq_min(s: Seq<int>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = seq_min(s.subrange(1, s.len()));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn lemma_seq_min_properties(s: Seq<int>)
    requires s.len() > 0
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s),
        forall|i: int| 0 <= i < s.len() ==> seq_min(s) <= s[i]
{
    if s.len() == 1 {
        assert(s[0] == seq_min(s));
    } else {
        lemma_seq_min_properties(s.subrange(1, s.len()));
    }
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
    /* code modified by LLM (iteration 5): Fixed compilation error by wrapping ghost operations in proof blocks */
    let mut best_entrance: i8 = 1;
    
    let ghost a_seq = a@.map(|i, x: i8| x as int);
    let ghost n_int = n as int;
    
    proof {
        let best_cc = compute_cc(n_int, a_seq, 0);
    }
    
    let mut idx: i8 = 1;
    while idx < n
        invariant
            1 <= idx <= n,
            1 <= best_entrance <= idx,
            forall|j: int| 0 <= j < idx ==> {
                let ccj = compute_cc(n_int, a_seq, j);
                let ccbest = compute_cc(n_int, a_seq, (best_entrance - 1) as int);
                ccbest <= ccj && (ccbest < ccj || (best_entrance - 1) as int <= j)
            },
        decreases n - idx
    {
        proof {
            let current_cc = compute_cc(n_int, a_seq, idx as int);
            let best_cc = compute_cc(n_int, a_seq, (best_entrance - 1) as int);
            
            if current_cc < best_cc || (current_cc == best_cc && idx < best_entrance) {
                best_entrance = idx + 1;
            }
        }
        
        if a@[idx as int] - idx as int < a@[(best_entrance - 1) as int] - (best_entrance - 1) as int {
            best_entrance = idx + 1;
        } else if a@[idx as int] - idx as int == a@[(best_entrance - 1) as int] - (best_entrance - 1) as int && idx < best_entrance {
            best_entrance = idx + 1;
        }
        
        idx = idx + 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < n_int ==> {
            let ccbest = compute_cc(n_int, a_seq, (best_entrance - 1) as int);
            let ccj = compute_cc(n_int, a_seq, j);
            ccbest <= ccj && (ccbest < ccj || (best_entrance - 1) as int <= j)
        });
    }
    
    best_entrance
}
// </vc-code>


}

fn main() {}