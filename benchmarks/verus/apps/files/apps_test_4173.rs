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
fn solve(queries: Seq<(int, int, int)>) -> (results: Seq<int>)
    requires 
        forall|i: int| 0 <= i < queries.len() ==> valid_query(queries[i])
    ensures 
        results.len() == queries.len(),
        forall|i: int| 0 <= i < queries.len() ==> {
            let n = queries[i].0;
            let a = queries[i].1;
            let b = queries[i].2;
            results[i] == (if n % 2 == 0 {
                if n * a <= (n / 2) * b { n * a } else { (n / 2) * b }
            } else {
                if n * a <= (n / 2) * b + a { n * a } else { (n / 2) * b + a }
            })
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}