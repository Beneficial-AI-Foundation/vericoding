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
proof fn lemma_nat_to_int_conversion(n_val: i8)
    requires n_val >= 0,
    ensures (n_val as int) >= 0
{
}

proof fn lemma_div_4_cases(n: int)
    requires n >= 1,
    ensures
        n % 4 == 0 ==> max_composite_summands(n) == n / 4,
        n % 4 == 1 ==> (n / 4 >= 2 ==> max_composite_summands(n) == n / 4 - 1),
        n % 4 == 2 ==> (n / 4 >= 1 ==> max_composite_summands(n) == n / 4),
        n % 4 == 3 ==> (n / 4 >= 3 ==> max_composite_summands(n) == n / 4 - 1),
        max_composite_summands(n) >= -1
{
}

proof fn lemma_composite_exists()
    ensures forall|x: int| x >= 4 ==> exists|k: int| 2 <= k < x && #[trigger] (x % k) == 0
{
}

proof fn lemma_max_composite_valid(n: int)
    requires n >= 1,
    ensures max_composite_summands(n) >= -1
{
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed lemma call syntax */
    let mut results = Vec::new();
    let mut i = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            valid_result(queries@.map(|j, x: i8| x as int).subrange(0, i as int), results@.map(|j, x: i8| x as int)),
            forall|j: int| 0 <= j < i ==> results@[j] >= -1
    {
        let n_val = queries[i];
        ghost { lemma_nat_to_int_conversion(n_val); }
        
        let result = if n_val % 4 == 0 {
            n_val / 4
        } else if n_val % 4 == 1 && n_val / 4 >= 2 {
            n_val / 4 - 1
        } else if n_val % 4 == 2 && n_val / 4 >= 1 {
            n_val / 4
        } else if n_val % 4 == 3 && n_val / 4 >= 3 {
            n_val / 4 - 1
        } else {
            -1
        };
        
        results.push(result as i8);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}