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
/* helper modified by LLM (iteration 5): proof of bounds for count_helper using Vec input */
proof fn count_helper_bounds(arrv: &Vec<i8>, i: int, count1: int, count2: int, temp1: int, temp2: int)
    requires
        0 <= i && i <= arrv.len() as int,
    ensures
        0 <= count_helper(arrv@.map(|j: int, x: i8| x as int), i, count1, count2, temp1, temp2),
        count_helper(arrv@.map(|j: int, x: i8| x as int), i, count1, count2, temp1, temp2) <= arrv.len() as int - i,
    decreases
        arrv.len() as int - i
{
    if i == arrv.len() as int {
        proof { }
    } else {
        let idx: usize = i as usize;
        let ai: int = arrv[idx] as int;
        let contribution: int =
            if i % 2 == 0 {
                let val1 = temp1 + count2 - temp2;
                let val2 = temp2 + count1 - temp1 - ai;
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1 + count2 - temp2 - ai;
                let val2 = temp2 + count1 - temp1;
                if val1 == val2 { 1 } else { 0 }
            };
        let new_temp1 = if i % 2 == 0 { temp1 + ai } else { temp1 };
        let new_temp2 = if i % 2 == 1 { temp2 + ai } else { temp2 };
        count_helper_bounds(arrv, i + 1, count1, count2, new_temp1, new_temp2);
        proof {
            assert(contribution == 0 || contribution == 1);
            assert(0 <= contribution);
            assert(contribution <= 1);
            assert(0 <= count_helper(arrv@.map(|j: int, x: i8| x as int), i + 1, count1, count2, new_temp1, new_temp2));
            assert(count_helper(arrv@.map(|j: int, x: i8| x as int), i + 1, count1, count2, new_temp1, new_temp2) <= arrv.len() as int - (i + 1));
            assert(count_helper(arrv@.map(|j: int, x: i8| x as int), i, count1, count2, temp1, temp2) == contribution + count_helper(arrv@.map(|j: int, x: i8| x as int), i + 1, count1, count2, new_temp1, new_temp2));
            assert(0 <= count_helper(arrv@.map(|j: int, x: i8| x as int), i, count1, count2, temp1, temp2));
            assert(count_helper(arrv@.map(|j: int, x: i8| x as int), i, count1, count2, temp1, temp2) <= arrv.len() as int - i);
        }
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
    /* code modified by LLM (iteration 5): compute with machine integers and relate to spec in a proof block */
    let mut count1_i: i64 = 0;
    let mut count2_i: i64 = 0;
    let mut idx: usize = 0;
    while idx < arr.len() {
        if idx % 2 == 0 {
            count1_i += arr[idx] as i64;
        } else {
            count2_i += arr[idx] as i64;
        }
        idx += 1;
    }

    let mut i: usize = 0;
    let mut temp1_i: i64 = 0;
    let mut temp2_i: i64 = 0;
    let mut acc_i: i64 = 0;

    while i < arr.len()
        invariant
            0 <= i as int && i as int <= arr.len() as int,
            acc_i as int + count_helper(arr@.map(|j: int, x: i8| x as int), i as int, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), temp1_i as int, temp2_i as int) == count_helper(arr@.map(|j: int, x: i8| x as int), 0, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), 0, 0),
        decreases
            (arr.len() as int) - i as int
    {
        let ai: i64 = arr[i] as i64;
        let contribution: i64 =
            if i % 2 == 0 {
                let val1 = temp1_i + count2_i - temp2_i;
                let val2 = temp2_i + count1_i - temp1_i - ai;
                if val1 == val2 { 1 } else { 0 }
            } else {
                let val1 = temp1_i + count2_i - temp2_i - ai;
                let val2 = temp2_i + count1_i - temp1_i;
                if val1 == val2 { 1 } else { 0 }
            };
        let new_temp1 = if i % 2 == 0 { temp1_i + ai } else { temp1_i };
        let new_temp2 = if i % 2 == 1 { temp2_i + ai } else { temp2_i };

        acc_i = acc_i + contribution;
        temp1_i = new_temp1;
        temp2_i = new_temp2;
        i += 1;
    }

    proof {
        assert(i == arr.len());
        assert(acc_i as int + count_helper(arr@.map(|j: int, x: i8| x as int), i as int, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), temp1_i as int, temp2_i as int) == count_helper(arr@.map(|j: int, x: i8| x as int), 0, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), 0, 0));
        assert(count_helper(arr@.map(|j: int, x: i8| x as int), arr.len() as int, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), temp1_i as int, temp2_i as int) == 0);
        assert(acc_i as int == count_helper(arr@.map(|j: int, x: i8| x as int), 0, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), 0, 0));
        count_helper_bounds(&arr, 0, sum_even_indices(arr@.map(|j: int, x: i8| x as int), 0), sum_odd_indices(arr@.map(|j: int, x: i8| x as int), 0), 0, 0);
        assert(0 <= acc_i as int && acc_i as int <= arr.len() as int);
    }

    let result: i8 = acc_i as i8;
    result
}

// </vc-code>


}

fn main() {}