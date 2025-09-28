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
/* helper modified by LLM (iteration 5): Fixed compute_cost to avoid using int in exec code */
fn compute_cost(n: i8, a: i8, b: i8) -> i8
    requires
        n > 0, a > 0, b > 0,
    ensures
        result as int == min_cost_for_query(n as int, a as int, b as int),
{
    if n % 2 == 0 {
        let n_half = n / 2;
        let cost_all = n.wrapping_mul(a);
        let cost_mix = n_half.wrapping_mul(b);
        if cost_all <= cost_mix { cost_all } else { cost_mix }
    } else {
        let n_half = n / 2;
        let cost_all = n.wrapping_mul(a);
        let cost_mix = n_half.wrapping_mul(b).wrapping_add(a);
        if cost_all <= cost_mix { cost_all } else { cost_mix }
    }
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
{
    /* code modified by LLM (iteration 5): Use exec code to avoid int conversions */
    let mut results = Vec::new();
    let mut i: usize = 0;
    let queries_len = queries.len();
    while i < queries_len
        invariant
            i <= queries@.len(),
            results@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let q = queries@[j];
                let n = q.0 as int;
                let a = q.1 as int;
                let b = q.2 as int;
                results@[j] as int == min_cost_for_query(n, a, b)
            },
        decreases queries_len - i,
    {
        let query = queries.index(i);
        let cost = compute_cost(query.0, query.1, query.2);
        results.push(cost);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}