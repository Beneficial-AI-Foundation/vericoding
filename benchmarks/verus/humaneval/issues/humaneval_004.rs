// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<f64>) -> f64
    decreases numbers.len()
{
    if numbers.len() == 0 {
        0.0
    } else {
        numbers[0] + sum(numbers.drop_first())
    }
}

spec fn abs(x: f64) -> f64 {
    if x >= 0.0 { x } else { -x }
}

spec fn valid_input(numbers: Seq<f64>) -> bool {
    numbers.len() > 0
}

spec fn arithmetic_mean(numbers: Seq<f64>) -> f64 {
    sum(numbers) / (numbers.len() as f64)
}

spec fn absolute_deviations(numbers: Seq<f64>) -> Seq<f64> {
    Seq::new(numbers.len(), |i: int| abs(numbers[i] - arithmetic_mean(numbers)))
}

spec fn mad(numbers: Seq<f64>) -> f64 {
    sum(absolute_deviations(numbers)) / (numbers.len() as f64)
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_non_negative(numbers: Seq<f64>)
    requires forall|i: int| 0 <= i < numbers.len() ==> numbers[i] >= 0.0,
    ensures sum(numbers) >= 0.0,
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else {
        sum_non_negative(numbers.drop_first());
    }
}
// </vc-helpers>

// <vc-spec>
fn mean_absolute_deviation(numbers: Vec<f64>) -> (result: f64)
    requires valid_input(numbers@)
    ensures result >= 0.0 && result == mad(numbers@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}