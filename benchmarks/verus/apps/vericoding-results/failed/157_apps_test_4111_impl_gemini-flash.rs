// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n && forall|i: int| 0 <= i < n ==> arr[i] >= 1
}

spec fn sum_even_indices(arr: Seq<int>, start: int) -> int
    decreases arr.len() - start when 0 <= start <= arr.len()
{
    if start == arr.len() {
        0
    } else {
        let contribution = if start % 2 == 0 { arr[start] } else { 0 };
        contribution + sum_even_indices(arr, start + 1)
    }
}

spec fn sum_odd_indices(arr: Seq<int>, start: int) -> int
    decreases arr.len() - start when 0 <= start <= arr.len()
{
    if start == arr.len() {
        0
    } else {
        let contribution = if start % 2 == 1 { arr[start] } else { 0 };
        contribution + sum_odd_indices(arr, start + 1)
    }
}

spec fn count_balanced_removals(arr: Seq<int>) -> int {
    let n = arr.len();
    if n == 0 {
        0
    } else {
        count_helper(arr, 0, sum_even_indices(arr, 0), sum_odd_indices(arr, 0), 0, 0)
    }
}

spec fn count_helper(arr: Seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int) -> int
    decreases arr.len() - i when 0 <= i <= arr.len()
{
    if i == arr.len() {
        0
    } else {
        let contribution: int = 
            if i % 2 == 0 {
                let val1 = temp1 + count2 - temp2;
                let val2 = temp2 + count1 - temp1 - arr[i];
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1 + count2 - temp2 - arr[i];
                let val2 = temp2 + count1 - temp1;
                if val1 == val2 { 1 } else { 0 }
            };
        let new_temp1 = if i % 2 == 0 { temp1 + arr[i] } else { temp1 };
        let new_temp2 = if i % 2 == 1 { temp2 + arr[i] } else { temp2 };
        contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, arr@.map(|i: int, x: i8| x as int)),
    ensures 
        0 <= result as int <= n as int,
        result as int == count_balanced_removals(arr@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariants for both loops and corrected sum calculations */
    let vec_len = arr.len();
    if vec_len == 0 {
        return 0i8;
    }

    let mut total_even_sum: i64 = 0;
    let mut total_odd_sum: i64 = 0;

    // Calculate initial total sums
    let mut i: usize = 0;
    while i < vec_len
        invariant
            0 <= i && i <= vec_len,
            total_even_sum == sum_even_indices(arr@.map(|j, x| x as int), 0) - sum_even_indices(arr@.map(|j, x| x as int), i as int),
            total_odd_sum == sum_odd_indices(arr@.map(|j, x| x as int), 0) - sum_odd_indices(arr@.map(|j, x| x as int), i as int),
            arr.len() == vec_len,
        decreases vec_len - i
    {
        let val: i64 = arr[i] as i64;
        if i % 2 == 0 {
            total_even_sum = total_even_sum + val;
        } else {
            total_odd_sum = total_odd_sum + val;
        }
        i = i + 1;
    }

    let mut count: i8 = 0;
    let mut current_even_sum: i64 = 0;
    let mut current_odd_sum: i64 = 0;

    let mut i: usize = 0;
    while i < vec_len
        invariant
            0 <= i && i <= vec_len,
            current_even_sum == sum_even_indices(arr@.map(|j, x| x as int), 0) - sum_even_indices(arr@.map(|j, x| x as int), i as int),
            current_odd_sum == sum_odd_indices(arr@.map(|j, x| x as int), 0) - sum_odd_indices(arr@.map(|j, x| x as int), i as int),
            count as int == count_helper(arr@.map(|k, x| x as int), 0, sum_even_indices(arr@.map(|k, x| x as int), 0), sum_odd_indices(arr@.map(|k, x| x as int), 0), 0, 0) - count_helper(arr@.map(|k, x| x as int), i as int, sum_even_indices(arr@.map(|k, x| x as int), 0), sum_odd_indices(arr@.map(|k, x| k as int), 0), current_even_sum as int, current_odd_sum as int),
            arr.len() == vec_len,
        decreases vec_len - i
    {
        let val_at_i: i64 = arr[i] as i64;

        if i % 2 == 0 {
            let removed_even_sum = total_even_sum - val_at_i;

            let left_even_sum = current_even_sum;
            let left_odd_sum = current_odd_sum;

            let right_even_sum = total_odd_sum - left_odd_sum;
            let right_odd_sum = removed_even_sum - left_even_sum;

            if left_even_sum + right_even_sum == left_odd_sum + right_odd_sum {
                count = count + 1;
            }
            current_even_sum = current_even_sum + val_at_i;
        } else {
            let removed_odd_sum = total_odd_sum - val_at_i;

            let left_even_sum = current_even_sum;
            let left_odd_sum = current_odd_sum;

            let right_even_sum = removed_odd_sum - left_odd_sum;
            let right_odd_sum = total_even_sum - left_even_sum;
            
            if left_even_sum + right_even_sum == left_odd_sum + right_odd_sum {
                count = count + 1;
            }
            current_odd_sum = current_odd_sum + val_at_i;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}