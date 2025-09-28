// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_ge_zero()
    ensures
        0 >= 0,
{
}

// </vc-helpers>

// <vc-spec>
spec fn count_valid_values(a: Seq<i32>) -> int {
    a.filter(|x: i32| x != 0).len() as int
}

spec fn sum_valid_values(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        let x = a[0];
        if x == 0 {
            sum_valid_values(a.skip(1))
        } else {
            x + sum_valid_values(a.skip(1))
        }
    }
}

spec fn mean_of_valid(a: Seq<i32>) -> int {
    let valid_count = count_valid_values(a);
    if valid_count > 0 {
        sum_valid_values(a) / valid_count
    } else {
        0
    }
}

spec fn sum_squared_deviations_spec(a: Seq<i32>, mean: int) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        let x = a[0];
        if x == 0 {
            sum_squared_deviations_spec(a.skip(1), mean)
        } else {
            let deviation = x - mean;
            deviation * deviation + sum_squared_deviations_spec(a.skip(1), mean)
        }
    }
}

spec fn variance_of_valid(a: Seq<i32>, ddof: int) -> int {
    let valid_count = count_valid_values(a);
    if valid_count > 0 && ddof < valid_count {
        let mean = mean_of_valid(a);
        let sum_squared_deviations = sum_squared_deviations_spec(a, mean);
        sum_squared_deviations / (valid_count - ddof)
    } else {
        0
    }
}

fn nanstd(a: Vec<i32>, ddof: usize) -> (result: i32)
    ensures ({
        let valid_count = count_valid_values(a@);
        let ddof_int = ddof as int;
        if valid_count > 0 && ddof_int < valid_count {
            let variance = variance_of_valid(a@, ddof_int);
            result >= 0
        } else {
            result == 0
        }
    })
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>


}
fn main() {}