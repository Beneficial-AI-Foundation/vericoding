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
    /* code modified by LLM (iteration 4): Fix compilation errors by removing 'as int' casts from exec code; compute prefix sums using i32 and cast to int only in proof assertions */
    let mut results = Vec::new();
    for i in 0..queries.len()
        invariant
            results@.len() == i as int,
            forall|j: int| 0 <= j < i ==> results@[j] as int == prefix_sum(queries@[j].1 as int) - prefix_sum(queries@[j].0 as int - 1),
    {
        let l = queries[i].0;
        let r = queries[i].1;
        let l_i32 = l as i32;
        let r_i32 = r as i32;
        let l_minus_1_i32 = l_i32 - 1;
        let prefix_r_i32 = if (r_i32 % 2) == 0 { r_i32 / 2 } else { - (r_i32 + 1) / 2 };
        let prefix_l_minus_1_i32 = if (l_minus_1_i32 % 2) == 0 { l_minus_1_i32 / 2 } else { - (l_minus_1_i32 + 1) / 2 };
        let sum_i32 = prefix_r_i32 - prefix_l_minus_1_i32;
        proof {
            assert(prefix_r_i32 as int == prefix_sum(r_i32 as int));
            assert(prefix_l_minus_1_i32 as int == prefix_sum(l_minus_1_i32 as int));
            assert(sum_i32 as int == prefix_sum(r_i32 as int) - prefix_sum(l_minus_1_i32 as int));
        }
        results.push(sum_i32 as i8);
    }
    results
}
// </vc-code>


}

fn main() {}