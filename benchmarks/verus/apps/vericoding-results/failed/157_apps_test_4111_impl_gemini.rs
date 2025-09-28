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
/* helper modified by LLM (iteration 3): added requires, cleaned up spec functions and fixed lemma syntax */
spec fn sum_prefix_even(arr: Seq<int>, k: int) -> int
    requires 0 <= k <= arr.len()
    decreases k
{
    if k == 0 {
        0
    } else {
        sum_prefix_even(arr, k - 1) + if (k - 1) % 2 == 0 { arr[k - 1] } else { 0 }
    }
}

/* helper modified by LLM (iteration 3): added requires, cleaned up spec functions and fixed lemma syntax */
spec fn sum_prefix_odd(arr: Seq<int>, k: int) -> int
    requires 0 <= k <= arr.len()
    decreases k
{
    if k == 0 {
        0
    } else {
        sum_prefix_odd(arr, k - 1) + if (k - 1) % 2 == 1 { arr[k - 1] } else { 0 }
    }
}

/* helper modified by LLM (iteration 3): added requires, cleaned up spec functions and fixed lemma syntax */
proof fn lemma_sum_even_split(arr: Seq<int>, i: int)
    requires 0 <= i <= arr.len()
    ensures sum_even_indices(arr, 0) == sum_prefix_even(arr, i) + sum_even_indices(arr, i)
    decreases i
{
    if i > 0 {
        lemma_sum_even_split(arr, i - 1);
    }
}

/* helper modified by LLM (iteration 3): added requires, cleaned up spec functions and fixed lemma syntax */
proof fn lemma_sum_odd_split(arr: Seq<int>, i: int)
    requires 0 <= i <= arr.len()
    ensures sum_odd_indices(arr, 0) == sum_prefix_odd(arr, i) + sum_odd_indices(arr, i)
    decreases i
{
    if i > 0 {
        lemma_sum_odd_split(arr, i - 1);
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
    /* code modified by LLM (iteration 3): no change, fixing compile error in helpers first */
    let arr_int = arr@.map(|_i: int, x: i8| x as int);
    let n_int = n as int;

    let mut j: int = 0;
    let mut count1: int = 0;
    let mut count2: int = 0;
    while j < n_int
        invariant
            0 <= j <= n_int,
            arr_int == arr@.map(|_i: int, x: i8| x as int),
            count1 == sum_prefix_even(arr_int, j),
            count2 == sum_prefix_odd(arr_int, j),
        decreases n_int - j
    {
        if j % 2 == 0 {
            count1 = count1 + arr_int[j];
        } else {
            count2 = count2 + arr_int[j];
        }
        j = j + 1;
    }

    proof {
        lemma_sum_even_split(arr_int, n_int);
        lemma_sum_odd_split(arr_int, n_int);
    }
    
    let mut i: int = 0;
    let mut result: int = 0;
    let mut temp1: int = 0;
    let mut temp2: int = 0;

    while i < n_int
        invariant
            0 <= i <= n_int,
            arr_int == arr@.map(|_i: int, x: i8| x as int),
            count1 == sum_even_indices(arr_int, 0),
            count2 == sum_odd_indices(arr_int, 0),
            temp1 == sum_prefix_even(arr_int, i),
            temp2 == sum_prefix_odd(arr_int, i),
            count_balanced_removals(arr_int) == 
                result + count_helper(arr_int, i, count1, count2, temp1, temp2),
            0 <= result <= i,
        decreases n_int - i
    {
        let val1: int;
        let val2: int;

        if i % 2 == 0 {
            val1 = temp1 + count2 - temp2;
            val2 = temp2 + count1 - temp1 - arr_int[i];
        } else {
            val1 = temp1 + count2 - temp2 - arr_int[i];
            val2 = temp2 + count1 - temp1;
        }

        let contribution = if val1 == val2 { 1 } else { 0 };
        
        proof {
            let next_temp1 = if i % 2 == 0 { temp1 + arr_int[i] } else { temp1 };
            let next_temp2 = if i % 2 == 1 { temp2 + arr_int[i] } else { temp2 };
            assert(count_helper(arr_int, i, count1, count2, temp1, temp2) ==
                   contribution + count_helper(arr_int, i + 1, count1, count2, next_temp1, next_temp2));
        }
        
        if val1 == val2 {
            result = result + 1;
        }

        if i % 2 == 0 {
            temp1 = temp1 + arr_int[i];
        } else {
            temp2 = temp2 + arr_int[i];
        }
        i = i + 1;
    }

    return result as i8;
}
// </vc-code>


}

fn main() {}