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
fn compute_max_composite(n: i64) -> i64
    requires
        n >= 1,
    ensures
        result == max_composite_summands(n as int),
        result >= -1,
{
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
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed forall syntax in invariant by removing invalid attribute */
    let mut results = Vec::<i8>::with_capacity(queries.len());
    let mut i = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results@[j] as int == max_composite_summands(queries@[j] as int),
        decreases
            queries.len() - i,
    {
        let q_int: i64 = queries[i] as i64;
        let res_int = compute_max_composite(q_int);
        let res = res_int as i8;
        proof {
            assert(res_int >= -1);
        }
        results.push(res);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}