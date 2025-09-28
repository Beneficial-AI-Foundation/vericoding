// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] heights[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] heights[i] < heights[i+1])
}

spec fn valid_output(n: int, result: Seq<int>) -> bool {
    result.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] <= result[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i+1] - result[i] <= 1)
}

spec fn is_stable(result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < result.len()-1 ==> !(#[trigger] result[i] + 2 <= result[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed compilation error by adding empty body for lemma.] */
proof fn lemma_sum_seq_map<T>(s: Seq<T>)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, heights@.map(|i, v| v as int))
    ensures 
        valid_output(n as int, result@.map(|i, v| v as int)) &&
        sum_seq(result@.map(|i, v| v as int)) == sum_seq(heights@.map(|i, v| v as int)) &&
        is_stable(result@.map(|i, v| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [refactored the solution to use direct sum calculation for `total_sum_i64` and removed unnecessary lemmas, still working on the filling process] */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let mut total_sum_i64: i64 = 0;
    let n_usize = n as usize;
    let ghost n_int: int = n as int;

    let ghost initial_sum = heights@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x) ;

    let mut idx: int = 0;
    while idx < n_int
        invariant
            0 <= idx <= n_int,
            result_vec.len() == idx as usize,
            total_sum_i64 == result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x) as i64,
            (forall|i: int| 0 <= i < idx ==> result_vec@[i] >= 0),
            (forall|i: int| 0 <= i < idx - 1 ==> result_vec@[i] as int <= result_vec@[i+1] as int),
            (forall|i: int| 0 <= i < idx - 1 ==> result_vec@[i+1] as int - result_vec@[i] as int <= 1)
        decreases n_int - idx
    {
        let curr_val_int: int;
        if idx == 0 {
            curr_val_int = heights@[idx] as int;
        } else {
            curr_val_int = if result_vec@[idx - 1] as int > heights@[idx] as int {
                result_vec@[idx - 1] as int
            } else {
                heights@[idx] as int
            };
        }

        let mut final_curr_val_int = curr_val_int;
        if idx > 0 {
            if final_curr_val_int > result_vec@[idx-1] as int + 1 {
                final_curr_val_int = result_vec@[idx-1] as int + 1;
            }
        }

        result_vec.push(final_curr_val_int as i8);
        total_sum_i64 = total_sum_i64 + final_curr_val_int as i64;

        idx = idx + 1;
    }
    
    let ghost mut diff: int = initial_sum - result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x);

    let mut k: int = 0;
    while k < n_int
        invariant
            0 <= k <= n_int,
            result_vec.len() == n_usize,
            total_sum_i64 == result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x) as i64,
            (forall|i: int| 0 <= i < n_int ==> result_vec@[i] >= 0),
            (forall|i: int| 0 <= i < n_int - 1 ==> result_vec@[i] as int <= result_vec@[i+1] as int),
            (forall|i: int| 0 <= i < n_int - 1 ==> result_vec@[i+1] as int - result_vec@[i] as int <= 1),
            diff == initial_sum - result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x)
        decreases n_int - k
    {
        while diff > 0 && k < n_int
            invariant
                0 <= k < n_int,
                result_vec.len() == n_usize,
                total_sum_i64 == result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x) as i64,
                (forall|i: int| 0 <= i < n_int ==> result_vec@[i] >= 0),
                (forall|i: int| 0 <= i < n_int - 1 ==> result_vec@[i] as int <= result_vec@[i+1] as int),
                (forall|i: int| 0 <= i < n_int - 1 ==> result_vec@[i+1] as int - result_vec@[i] as int <= 1),
                diff == initial_sum - result_vec@.map(|_i, v| v as int).fold_left(0, |acc: int, x: int| acc + x)
            decreases diff
        {
            let original_val_int = result_vec@[k] as int;
            if k == 0 || result_vec@[k] as int <= result_vec@[k-1] as int + 1 {
                if original_val_int > 0 {
                    result_vec.set(k as usize, (original_val_int - 1) as i8);
                    diff = diff - 1;
                    total_sum_i64 = total_sum_i64 - 1;
                }
            }
        }
        k = k + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}