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
    /* code modified by LLM (iteration 5): using i32 to avoid overflow in i8 arithmetic */
    let mut results = Vec::new();
    let mut i: usize = 0;
    
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let n = queries@[j].0 as int;
                let a = queries@[j].1 as int;
                let b = queries@[j].2 as int;
                #[trigger] results@[j] as int == (if n % 2 == 0 {
                    if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
                } else {
                    if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
                })
            },
            forall|j: int| 0 <= j < queries@.len() ==> #[trigger] valid_query((queries@[j].0 as int, queries@[j].1 as int, queries@[j].2 as int)),
        decreases queries.len() - i
    {
        let (n, a, b) = queries[i];
        
        // Convert to i32 to avoid overflow
        let n_i32 = n as i32;
        let a_i32 = a as i32;
        let b_i32 = b as i32;
        
        let cost_i32 = if n_i32 % 2 == 0 {
            if n_i32 * a_i32 <= (n_i32 / 2) * b_i32 {
                n_i32 * a_i32
            } else {
                (n_i32 / 2) * b_i32
            }
        } else {
            if n_i32 * a_i32 <= (n_i32 / 2) * b_i32 + a_i32 {
                n_i32 * a_i32
            } else {
                (n_i32 / 2) * b_i32 + a_i32
            }
        };
        
        let cost = cost_i32 as i8;
        results.push(cost);
        i = i + 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}