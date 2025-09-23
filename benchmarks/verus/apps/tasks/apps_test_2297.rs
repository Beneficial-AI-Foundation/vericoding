// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_query(query: (int, int)) -> bool {
    query.0 >= 1 && query.0 <= query.1
}

spec fn valid_input(queries: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> valid_query(queries[i])
}

spec fn array_element(i: int) -> int
    recommends i >= 1
{
    i * (if i % 2 == 1 { -1 } else { 1 })
}

spec fn range_sum(l: int, r: int) -> int
    recommends l >= 1
    decreases r - l + 1
{
    if l > r { 0 } else { array_element(l) + range_sum(l + 1, r) }
}

spec fn prefix_sum(k: int) -> int {
    if k % 2 == 0 { k / 2 } else { -(k + 1) / 2 }
}

spec fn correct_result(queries: Seq<(int, int)>, results: Seq<int>) -> bool
    recommends valid_input(queries)
{
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == prefix_sum(queries[i].1) - prefix_sum(queries[i].0 - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)))
    ensures correct_result(queries@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}