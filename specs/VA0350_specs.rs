// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(queries: Seq<int>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> queries[i] >= 2
}

spec fn min_additional_matches(n: int) -> int
    recommends n >= 2
{
    if n >= 4 { n % 2 } else { 4 - n }
}

spec fn valid_result(queries: Seq<int>, results: Seq<int>) -> bool
    recommends valid_input(queries)
{
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == min_additional_matches(queries[i])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i: int, x: i8| x as int))
    ensures valid_result(queries@.map(|i: int, x: i8| x as int), results@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}