// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    decreases n when n > 0
{
    if n > 0 && n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    decreases a.len() - i when 0 <= i <= a.len()
{
    if 0 <= i < a.len() && (forall|j: int| 0 <= j < a.len() ==> a[j] > 0) {
        count_factors_of_two(a[i]) + sum_factors(a, i + 1)
    } else if i == a.len() {
        0
    } else {
        0
    }
}

spec fn max_operations(a: Seq<int>) -> int {
    if valid_input(a) { sum_factors(a, 0) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no change, just updating comment for new iteration */
fn count_factors_of_two_iter(n: i8) -> (count: i8)
    requires
        n > 0,
    ensures
        count >= 0,
        count as int == count_factors_of_two(n as int),
{
    let mut current_n = n;
    let mut num_ops: i8 = 0;
    while current_n > 0 && current_n % 2 == 0
        invariant
            n > 0,
            current_n > 0,
            num_ops >= 0,
            count_factors_of_two(n as int) == num_ops as int + count_factors_of_two(current_n as int),
        decreases current_n
    {
        num_ops = num_ops + 1;
        current_n = current_n / 2;
    }
    num_ops
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result >= 0,
        result as int == max_operations(a@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation error (let ghost) and made map closure consistent */
{
    let mut total_ops: i8 = 0;
    let mut i: usize = 0;
    let ghost a_int = a@.map(|i, x| x as int);
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a@.map(|i, x| x as int) == a_int,
            valid_input(a_int),
            total_ops >= 0,
            total_ops as int == sum_factors(a_int, 0) - sum_factors(a_int, i as int),
        decreases a.len() - i
    {
        let ops = count_factors_of_two_iter(a[i]);
        total_ops = total_ops + ops;
        i = i + 1;
    }
    total_ops
}
// </vc-code>


}

fn main() {}