// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_composite(x: int) -> bool {
    x >= 4 && exists|k: int| 2 <= k < x && #[trigger] (x % k) == 0
}

spec fn valid_input(queries: Seq<int>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> queries[i] >= 1
}

spec fn max_composite_summands(n: int) -> int {
    if n % 4 == 0 {
        n / 4
    } else if n % 4 == 1 && n / 4 >= 2 {
        n / 4 - 1
    } else if n % 4 == 2 && n / 4 >= 1 {
        n / 4
    } else if n % 4 == 3 && n / 4 >= 3 {
        n / 4 - 1
    } else {
        -1
    }
}

spec fn valid_result(queries: Seq<int>, results: Seq<int>) -> bool {
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == max_composite_summands(queries[i]) &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] >= -1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed precondition to match calling context */
fn compute_max_composite_summands(n: i8) -> (result: i8)
    ensures 
        result as int == max_composite_summands(n as int),
        result as int >= -1
{
    let quotient = n / 4;
    let remainder = n % 4;
    if remainder == 0 {
        quotient
    } else if remainder == 1 && quotient >= 2 {
        quotient - 1
    } else if remainder == 2 && quotient >= 1 {
        quotient
    } else if remainder == 3 && quotient >= 3 {
        quotient - 1
    } else {
        -1
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed precondition issue by adding assertion */
{
    let mut results = Vec::new();
    for i in 0..queries.len()
        invariant
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j] as int == max_composite_summands(queries@[j] as int) && results[j] as int >= -1
    {
        let n = queries[i];
        assert(n as int >= 1); // Ensure precondition is satisfied
        let res = compute_max_composite_summands(n);
        results.push(res);
    }
    results
}
// </vc-code>


}

fn main() {}