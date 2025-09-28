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
/* helper modified by LLM (iteration 5): [fixed compilation error by using correct seq_lib lemma] */
proof fn lemma_sum_seq_push(s: Seq<int>, e: int)
    ensures sum_seq(s.push(e)) == sum_seq(s) + e,
    decreases s.len(),
{
    if s.len() > 0 {
        vstd::seq_lib::lemma_subrange_of_push_subrange_alt(s, e, 1);
        lemma_sum_seq_push(s.subrange(1, s.len()), e);
    }
}

/* helper modified by LLM (iteration 5): [fixed compilation errors by using correct seq_lib lemmas] */
fn compute_sum(n: i8, arr: &Vec<i8>) -> (sum: i32)
    requires
        valid_input(n as int, arr@.map(|i: int, x: i8| x as int)),
    ensures
        sum as int == sum_seq(arr@.map(|i: int, x: i8| x as int)),
{
    let mut sum: i32 = 0;
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            sum as int == sum_seq(arr@.map(|i: int, x: i8| x as int).subrange(0, i as int)),
        decreases n - i
    {
        proof {
            let arr_int = arr@.map(|i: int, x: i8| x as int);
            vstd::seq_lib::lemma_subrange_is_push(arr_int, i as int);
            lemma_sum_seq_push(arr_int.subrange(0, i as int), arr_int[i as int]);
        }

        let x = arr[i as usize];
        sum = sum + (x as i32);
        i = i + 1;
    }
    proof {
        let arr_int = arr@.map(|i:int, x:i8| x as int);
        vstd::seq_lib::lemma_subrange_equal(arr_int);
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [no changes required, logic is correct] */
{
    let total_sum = compute_sum(n, &arr);
    if total_sum.rem_euclid(n as i32) == 0 {
        n
    } else {
        n - 1
    }
}
// </vc-code>


}

fn main() {}