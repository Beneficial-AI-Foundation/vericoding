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
/* helper modified by LLM (iteration 5): Fixed lemma parameters and ghost variable declarations */
proof fn lemma_balances_are_equivalent(arr: Seq<int>, i: int, temp1: int, temp2: int)
    requires
        0 <= i <= arr.len(),
        temp1 == sum_even_indices(arr, 0) - sum_even_indices(arr, i),
        temp2 == sum_odd_indices(arr, 0) - sum_odd_indices(arr, i)
    ensures
        sum_even_indices(arr, 0) == temp1 + sum_even_indices(arr, i),
        sum_odd_indices(arr, 0) == temp2 + sum_odd_indices(arr, i)
{
}

proof fn get_remaining_sums(arr: Seq<int>, i: int) -> (remaining_odd: int, remaining_even: int)
    requires
        0 <= i <= arr.len()
    ensures
        remaining_odd == sum_odd_indices(arr, i),
        remaining_even == sum_even_indices(arr, i)
{
    (sum_odd_indices(arr, i), sum_even_indices(arr, i))
}
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
/* code modified by LLM (iteration 5): Fixed ghost variable extraction and type handling */
{
    let mut result: i8 = 0;
    let mut temp1: i64 = 0;
    let mut temp2: i64 = 0;
    
    let ghost arr_seq = arr@.map(|i: int, x: i8| x as int);
    let ghost total_even = sum_even_indices(arr_seq, 0);
    let ghost total_odd = sum_odd_indices(arr_seq, 0);
    
    for i in 0..n {
        let i_usize = i as usize;
        let val = arr[i_usize] as i64;
        
        proof {
            let ghost i_int = i as int;
            lemma_balances_are_equivalent(arr_seq, i_int, temp1 as int, temp2 as int);
        }
        
        proof {
            let ghost remaining = get_remaining_sums(arr_seq, (i + 1) as int);
            let ghost remaining_odd = remaining.0;
            let ghost remaining_even = remaining.1;
            
            let contribution = if i % 2 == 0 {
                let calculated_val1 = temp1 + (remaining_odd as i64);
                let calculated_val2 = temp2 + (remaining_even as i64) - val;
                if calculated_val1 == calculated_val2 { 1 } else { 0 }
            } else {
                let calculated_val1 = temp1 + (remaining_odd as i64) - val;
                let calculated_val2 = temp2 + (remaining_even as i64);
                if calculated_val1 == calculated_val2 { 1 } else { 0 }
            };
            
            result += contribution as i8;
        }
        
        if i % 2 == 0 {
            temp1 += val;
        } else {
            temp2 += val;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}