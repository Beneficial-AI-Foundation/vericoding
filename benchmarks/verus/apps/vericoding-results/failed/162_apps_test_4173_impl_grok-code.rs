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
/* helper modified by LLM (iteration 4): named result parameter in exec fn to resolve compilation error with 'result' in ensures */
exec fn min_via_if(cond: bool, val1: i32, val2: i32) -> (result: i32)
    ensures
        result == if cond { val1 } else { val2 }
{
    if cond { val1 } else { val2 }
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
/* code modified by LLM (iteration 4): no changes needed, compilation fixed */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            queries.len() <= 0x4FFF,
            0 <= i <= queries.len() as int,
            results@.len() == i as int,
            forall|k: int| 0 <= k < i ==> {
                let n = queries@[k].0 as int;
                let a = queries@[k].1 as int;
                let b = queries@[k].2 as int;
                let min_cost = if n % 2 == 0 {
                    if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
                } else {
                    if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
                };
                #[trigger] results@[k] == min_cost as i8
            },
        decreases (queries.len() as int) - i
    {
        let query = queries[i];
        let n = query.0 as i32;
        let a = query.1 as i32;
        let b = query.2 as i32;
        let cost1 = n * a;
        let cost2 = if n % 2 == 0 {
             (n / 2) * b
        } else {
             (n / 2) * b + a
        };
        let min_cost_i32 = min_via_if(cost1 <= cost2, cost1, cost2);
        let cost = min_cost_i32 as i8;
        results.push(cost);
        proof {
            assert(results@[i as int] == ((if n % 2 == 0 {
                if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
            } else {
                if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
            }) as i32) as i8);
        }
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}