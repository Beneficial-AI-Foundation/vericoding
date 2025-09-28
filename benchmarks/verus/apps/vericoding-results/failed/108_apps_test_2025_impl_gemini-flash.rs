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
/* helper modified by LLM (iteration 5): The previous helper block was empty. This is now also empty to reflect that no helper functions are needed for this problem. */

// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast `n_i8` to `int` for `max_composite_summands` to resolve type error. */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < queries.len()
        invariant
            0 <= i as int,
            i <= queries.len(),
            results.len() == i,
            // All prior results are correctly calculated based on max_composite_summands
            forall|j: int| 0 <= j < i ==> results@[j] == max_composite_summands(queries@[j] as int) as i8,
            // The input queries remain valid throughout the loop
            valid_input(queries@.map(|_, x: i8| x as int)),
    {
        let n_i8: i8 = queries[i];
        let n: int = n_i8 as int; // This casting is fine for _spec_ function consumption.

        let result_val_int: int = max_composite_summands(n);
        let result_val: i8;

        // The result of max_composite_summands could be negative or positive.
        // We need to ensure it fits into an i8.
        if result_val_int >= -128 && result_val_int <= 127 {
            result_val = result_val_int as i8;
        } else {
            // This case should ideally not be reached given valid_input constraints for this problem
            // However, for type safety, we need to handle it. Set to -1 which is a valid output.
            result_val = -1;
        }

        results.push(result_val);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}