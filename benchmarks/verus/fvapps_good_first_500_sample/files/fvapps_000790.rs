// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn filter_type_1_queries(queries: Seq<Seq<usize>>) -> Seq<Seq<usize>>
    decreases queries.len()
{
    if queries.len() == 0 {
        seq![]
    } else {
        let query = queries[0];
        let rest_filtered = filter_type_1_queries(queries.skip(1));
        if query.len() > 0 && query[0] == 1 {
            seq![query].add(rest_filtered)
        } else {
            rest_filtered
        }
    }
}

fn solve_mountain_queries(n: usize, mountains: Vec<usize>, queries: Vec<Vec<usize>>) -> (result: Vec<i32>)
    requires 
        n >= 2,
        mountains.len() == n,
    ensures 
        result.len() == filter_type_1_queries(queries@.map(|i: int, q: Vec<usize>| q@)).len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == -1 || result[i] >= 0),
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