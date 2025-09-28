// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_query(query: (int, int, int)) -> bool {
    query.0 > 0 && query.1 > 0 && query.2 > 0
}

spec fn min_cost_for_query(n: int, a: int, b: int) -> int
    recommends n > 0 && a > 0 && b > 0
{
    if n % 2 == 0 {
        if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
    } else {
        if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use int arithmetic to avoid overflow and match spec exactly */
exec fn compute_min_cost(n: i8, a: i8, b: i8) -> (cost: i8)
    requires valid_query((n as int, a as int, b as int))
    ensures cost as int == min_cost_for_query(n as int, a as int, b as int)
{
    let n_int = n as int;
    let a_int = a as int;
    let b_int = b as int;
    let cost_int = if n_int % 2 == 0 {
        if n_int * a_int <= (n_int / 2) * b_int {
            n_int * a_int
        } else {
            (n_int / 2) * b_int
        }
    } else {
        if n_int * a_int <= (n_int / 2) * b_int + a_int {
            n_int * a_int
        } else {
            (n_int / 2) * b_int + a_int
        }
    };
    proof {
        assert(cost_int == min_cost_for_query(n_int, a_int, b_int));
        assert(cost_int <= 127);
    }
    cost_int as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(i8, i8, i8)>) -> (results: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < queries@.len() ==> #[trigger] valid_query((queries@[i].0 as int, queries@[i].1 as int, queries@[i].2 as int))
    ensures 
        results@.len() == queries@.len() &&
        forall|i: int| 0 <= i < queries@.len() ==> {
            let n = queries@[i].0 as int;
            let a = queries@[i].1 as int;
            let b = queries@[i].2 as int;
            #[trigger] results@[i] as int == (if n % 2 == 0 {
                if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
            } else {
                if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
            })
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use the helper function and ensure bounds */
{
    let mut results = Vec::new();
    for i in 0..queries.len() {
        let (n, a, b) = queries[i];
        let cost = compute_min_cost(n, a, b);
        results.push(cost);
    }
    results
}
// </vc-code>


}

fn main() {}