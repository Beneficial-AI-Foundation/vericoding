// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn correct_result(n: int, arr: Seq<int>, result: int) -> bool {
    &&& (sum_seq(arr) % n == 0 ==> result == n)
    &&& (sum_seq(arr) % n != 0 ==> result == n - 1)
    &&& (result == n || result == n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use ghost variable for integer sequence and add bounds to prevent overflow */
fn compute_sum(arr: &Vec<i8>) -> (sum: i64)
    ensures (sum as int) == sum_seq(arr@.map(|i: int, x: i8| x as int))
{
    ghost let int_arr = arr@.map(|i: int, x: i8| x as int);
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            (total as int) == sum_seq(int_arr.subrange(0, i as int)),
            total <= (i as i64) * 127,
            total >= (i as i64) * (-128),
        decreases (arr.len() - i) as int
    {
        let x = arr[i] as i64;
        total = total + x;
        i += 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use integer arithmetic for modulo to match postcondition */
    let total = compute_sum(&arr);
    let total_int = total as int;
    let n_int = n as int;
    if total_int % n_int == 0 {
        n
    } else {
        n - 1
    }
}
// </vc-code>


}

fn main() {}