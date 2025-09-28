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
fn compute_cost(n_i8: i8, a_i8: i8, b_i8: i8) -> (cost: i32)
    requires
        n_i8 > 0,
        a_i8 > 0,
        b_i8 > 0,
    ensures
        cost == min_cost_for_query(n_i8 as int, a_i8 as int, b_i8 as int),
{
    let n = n_i8 as i32;
    let a = a_i8 as i32;
    let b = b_i8 as i32;
    if n % 2 == 0 {
        let cost1 = n * a;
        let cost2 = (n / 2) * b;
        if cost1 <= cost2 {
            cost1
        } else {
            cost2
        }
    } else {
        let cost1 = n * a;
        let cost2 = (n / 2) * b + a;
        if cost1 <= cost2 {
            cost1
        } else {
            cost2
        }
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
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries@.len(),
            results@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] results@[j] as int == min_cost_for_query(queries@[j].0 as int, queries@[j].1 as int, queries@[j].2 as int),
            forall|k: int| 0 <= k < queries@.len() ==> #[trigger] valid_query((queries@[k].0 as int, queries@[k].1 as int, queries@[k].2 as int)),
        decreases queries.len() - i
    {
        let n = queries[i].0;
        let a = queries[i].1;
        let b = queries[i].2;

        let cost = compute_cost(n, a, b);

        results.push(cost as i8);
        
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}