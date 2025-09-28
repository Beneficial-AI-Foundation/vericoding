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
    /* code modified by LLM (iteration 5): fixed array indexing with @ operator */
    if n == 0 {
        return 0;
    }
    
    let mut count1: i32 = 0;
    let mut count2: i32 = 0;
    
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            count1 == sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0) - sum_even_indices(arr@.map(|j: int, x: i8| x as int), i as int),
            count2 == sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0) - sum_odd_indices(arr@.map(|j: int, x: i8| x as int), i as int),
            count1 >= 0,
            count2 >= 0,
            count1 <= i32::MAX,
            count2 <= i32::MAX,
        decreases arr.len() - i
    {
        if i % 2 == 0 {
            assert(count1 + arr[i] as i32 <= i32::MAX);
            count1 = count1 + arr[i] as i32;
        } else {
            assert(count2 + arr[i] as i32 <= i32::MAX);
            count2 = count2 + arr[i] as i32;
        }
        i = i + 1;
    }
    
    let mut result: i8 = 0;
    let mut temp1: i32 = 0;
    let mut temp2: i32 = 0;
    
    i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            0 <= result <= i,
            result == count_helper(arr@.map(|j: int, x: i8| x as int), 0, count1 as int, count2 as int, 0, 0) - count_helper(arr@.map(|j: int, x: i8| x as int), i as int, count1 as int, count2 as int, temp1 as int, temp2 as int),
            temp1 == sum_even_indices(arr@.map(|j: int, x: i8| x as int).subrange(0, i as int), 0),
            temp2 == sum_odd_indices(arr@.map(|j: int, x: i8| x as int).subrange(0, i as int), 0),
            count1 == sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0),
            count2 == sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0),
            temp1 >= 0,
            temp2 >= 0,
            temp1 <= count1,
            temp2 <= count2,
        decreases arr.len() - i
    {
        if i % 2 == 0 {
            assert(temp1 + count2 >= temp2);
            assert(temp2 + count1 >= temp1 + arr[i] as i32);
            let val1 = temp1 + count2 - temp2;
            let val2 = temp2 + count1 - temp1 - arr[i] as i32;
            if val1 == val2 {
                result = result + 1;
            }
            temp1 = temp1 + arr[i] as i32;
        } else {
            assert(temp1 + count2 >= temp2 + arr[i] as i32);
            assert(temp2 + count1 >= temp1);
            let val1 = temp1 + count2 - temp2 - arr[i] as i32;
            let val2 = temp2 + count1 - temp1;
            if val1 == val2 {
                result = result + 1;
            }
            temp2 = temp2 + arr[i] as i32;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}