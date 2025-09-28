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
/* helper modified by LLM (iteration 2): added executable versions of spec functions with reordered spec clauses to fix compilation */ */
fn sum_even_exec(arr: &Vec<i8>, start: usize) -> i32
requires
start <= arr.len()
ensures
result as int == sum_even_indices(arr@.map(|i: int, x: i8| x as int), start as int)
decreases arr.len() - start when start <= arr.len()
{
if start == arr.len() {
0
} else {
let contribution = if start % 2 == 0 { arr[start] as i32 } else { 0 };
contribution + sum_even_exec(arr, start + 1)
}
}

fn sum_odd_exec(arr: &Vec<i8>, start: usize) -> i32
requires
start <= arr.len()
ensures
result as int == sum_odd_indices(arr@.map(|i: int, x: i8| x as int), start as int)
decreases arr.len() - start when start <= arr.len()
{
if start == arr.len() {
0
} else {
let contribution = if start % 2 == 1 { arr[start] as i32 } else { 0 };
contribution + sum_odd_exec(arr, start + 1)
}
}

fn count_helper_exec(arr: &Vec<i8>, i: usize, count1: i32, count2: i32, temp1: i32, temp2: i32) -> i32
decreases arr.len() - i when i <= arr.len()
requires
i <= arr.len(),
count1 as int == sum_even_indices(arr@.map(|i: int, x: i8| x as int), 0),
count2 as int == sum_odd_indices(arr@.map(|i: int, x: i8| x as int), 0)
ensures
result as int == count_helper(arr@.map(|i: int, x: i8| x as int), i as int, count1 as int, count2 as int, temp1 as int, temp2 as int)
{
if i == arr.len() {
0
} else {
let contribution: i32 =
if i % 2 == 0 {
let val1 = temp1 + count2 - temp2;
let val2 = temp2 + count1 - temp1 - (arr[i] as i32);
if val1 == val2 { 1 } else { 0 }
} else {
let val1 = temp1 + count2 - temp2 - (arr[i] as i32);
let val2 = temp2 + count1 - temp1;
if val1 == val2 { 1 } else { 0 }
};
let new_temp1 = if i % 2 == 0 { temp1 + (arr[i] as i32) } else { temp1 };
let new_temp2 = if i % 2 == 1 { temp2 + (arr[i] as i32) } else { temp2 };
contribution + count_helper_exec(arr, i + 1, count1, count2, new_temp1, new_temp2)
}
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
{
    /* code modified by LLM (iteration 2): compute even and odd sums, then use helper to count balanced removals and cast to i8 */
    let sum_even = sum_even_exec(&arr, 0);
    let sum_odd = sum_odd_exec(&arr, 0);
    let result_count = count_helper_exec(&arr, 0, sum_even, sum_odd, 0, 0);
    result_count as i8
}
// </vc-code>


}

fn main() {}