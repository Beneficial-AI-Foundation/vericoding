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
/* helper modified by LLM (iteration 5): No helpers are needed, as the previous iteration removed the `min_cost` helper that was redundant. */
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
    /* code modified by LLM (iteration 5): Ensured that types match, by keeping n,a,b for calculation as int while using n_i,a_i,b_i of type i8 for input into results. */
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let query_j = queries@[j];
                valid_query((query_j.0 as int, query_j.1 as int, query_j.2 as int))
            } ==> results@[j] as int == min_cost_for_query(queries@[j].0 as int, queries@[j].1 as int, queries@[j].2 as int),
        decreases queries.len() - i
    {
        let query_i = queries.get(i).unwrap();
        let n_i = query_i.0;
        let a_i = query_i.1;
        let b_i = query_i.2;

        let n = n_i as int;
        let a = a_i as int;
        let b = b_i as int;

        let cost_val_int: int;

        if n % 2 == 0 {
            if n * a <= (n / 2) * b {
                cost_val_int = n * a;
            } else {
                cost_val_int = (n / 2) * b;
            }
        } else {
            if n * a <= (n / 2) * b + a {
                cost_val_int = n * a;
            }
            else {
                cost_val_int = (n / 2) * b + a;
            }
        }

        results.push(cost_val_int as i8);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}