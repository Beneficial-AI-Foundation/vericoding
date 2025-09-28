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
lemma lemma_sum_even_indices_add(arr: Seq<int>, start: int, val: int)
    requires 0 <= start <= arr.len()
    ensures sum_even_indices(arr.push(val), start) == sum_even_indices(arr, start) + (if (start + arr.len()) % 2 == 0 { val } else { 0 })
{}

lemma lemma_sum_odd_indices_add(arr: Seq<int>, start: int, val: int)
    requires 0 <= start <= arr.len()
    ensures sum_odd_indices(arr.push(val), start) == sum_odd_indices(arr, start) + (if (start + arr.len()) % 2 == 1 { val } else { 0 })
{}

lemma lemma_count_helper_bounds(arr: Seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
    requires 0 <= i <= arr.len(), count1 >= 0, count2 >= 0
    ensures count_helper(arr, i, count1, count2, temp1, temp2) >= 0
    decreases arr.len() - i
{}

lemma lemma_count_balanced_removals_bounds(arr: Seq<int>)
    requires arr.len() >= 0
    ensures 0 <= count_balanced_removals(arr) <= arr.len()
{}
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
    let mut result: i8 = 0;
    let mut temp1: i32 = 0;
    let mut temp2: i32 = 0;
    let mut count1: i32 = 0;
    let mut count2: i32 = 0;
    
    let mut k: usize = 0;
    while k < arr.len()
        invariant
            k <= arr.len(),
            count1 == sum_even_indices(arr@.map(|i: int, x: i8| x as int), 0),
            count2 == sum_odd_indices(arr@.map(|i: int, x: i8| x as int), 0),
    {
        if k % 2 == 0 {
            count1 += arr[k] as i32;
        } else {
            count2 += arr[k] as i32;
        }
        k += 1;
    }
    
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            0 <= result <= i,
            temp1 == sum_even_indices(arr@.map(|i: int, x: i8| x as int), 0) - sum_even_indices(arr@.map(|i: int, x: i8| x as int), i as int),
            temp2 == sum_odd_indices(arr@.map(|i: int, x: i8| x as int), 0) - sum_odd_indices(arr@.map(|i: int, x: i8| x as int), i as int),
    {
        let val1: i32;
        let val2: i32;
        
        if i % 2 == 0 {
            val1 = temp1 + count2 - temp2;
            val2 = temp2 + count1 - temp1 - arr[i] as i32;
        } else {
            val1 = temp1 + count2 - temp2 - arr[i] as i32;
            val2 = temp2 + count1 - temp1;
        }
        
        if val1 == val2 {
            result += 1;
        }
        
        if i % 2 == 0 {
            temp1 += arr[i] as i32;
        } else {
            temp2 += arr[i] as i32;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}