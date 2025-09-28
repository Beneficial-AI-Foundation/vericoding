// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n && forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 1
}

spec fn valid_operations(operations: Seq<(int, int)>, n: int) -> bool {
    forall|op: (int, int)| operations.contains(op) ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
}

spec fn is_sorted_helper(arr: Seq<int>, i: int) -> bool 
    decreases arr.len() - i
{
    if i >= arr.len() - 1 {
        true
    } else {
        arr[i] <= arr[i + 1] && is_sorted_helper(arr, i + 1)
    }
}

spec fn is_sorted(arr: Seq<int>) -> bool {
    if arr.len() <= 1 {
        true
    } else {
        is_sorted_helper(arr, 0)
    }
}

spec fn swap_adjacent(arr: Seq<int>, i: int, j: int) -> Seq<int> {
    if i >= 0 && j >= 0 && i < arr.len() && j < arr.len() && j == i + 1 {
        arr.update(i, arr[j]).update(j, arr[i])
    } else {
        arr
    }
}

spec fn apply_operations(arr: Seq<int>, operations: Seq<(int, int)>) -> Seq<int>
    decreases operations.len()
{
    if operations.len() == 0 {
        arr
    } else {
        let op = operations[0];
        if 1 <= op.0 <= arr.len() && 1 <= op.1 <= arr.len() && op.1 == op.0 + 1 {
            let new_arr = swap_adjacent(arr, (op.0 - 1) as int, (op.1 - 1) as int);
            apply_operations(new_arr, operations.drop_first())
        } else {
            apply_operations(arr, operations.drop_first())
        }
    }
}

spec fn count_inversions(arr: Seq<int>) -> nat {
    /* Count of pairs (i, j) where i < j and arr[i] > arr[j] */
    0nat /* Placeholder implementation */
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused recursive inversion counter and simplified the inversion counter to count pairs (i, j) where i < j and arr[i] > arr[j]. */
spec fn count_inversions_spec(arr: Seq<int>) -> nat {
    let mut count = 0;
    if arr.len() <= 1 {
        0
    } else {
        let mut i = 0;
        while i < arr.len()
        decreases arr.len() - i
        {
            let mut j = i + 1;
            while j < arr.len()
            decreases arr.len() - j
            {
                if arr[i] > arr[j] {
                    count = count + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (operations: Vec<(i8, i8)>)
  requires 
      valid_input(n as int, arr@.map_values(|x: i8| x as int)),
  ensures 
      valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int) &&
      (is_sorted(apply_operations(arr@.map_values(|x: i8| x as int), operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)))) || operations.len() == 20000) &&
      operations.len() <= 20000 &&
      (is_sorted(arr@.map_values(|x: i8| x as int)) ==> operations.len() == 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error where `current_arr_core[k as usize]` was incorrectly typed. It should be `current_arr_core[k as int]`. */
{
    let mut current_arr_core = arr;
    let mut operations: Vec<(i8, i8)> = Vec::new();

    let N: usize = n as usize;

    if n == 0 { return operations; }

    let max_ops = 20000;

    let mut i: usize = 0;
    while i < N - 1 && operations.len() < max_ops
        invariant
            0 <= i && i <= N,
            current_arr_core.len() == N,
            operations.len() <= max_ops,
            n as int == N as int,
            // ghost invariant: the underlying speculative sequence has the same length as current_arr_core vector
            current_arr_core@.len() == N as int,
            forall |k: int| 0 <= k < N as int ==> current_arr_core@.map_values(|x: i8| x as int)[k] == current_arr_core[k as int] as int,
    {
        let mut swapped_in_pass = false;

        let mut j: usize = 0;
        while j < N - 1 - i && operations.len() < max_ops
            invariant
                0 <= j && j <= N - 1 - i,
                current_arr_core.len() == N,
                operations.len() <= max_ops,
                i <= N - 1,
                n as int == N as int,
                // ghost invariant: the underlying speculative sequence has the same length as current_arr_core vector
                current_arr_core@.len() == N as int,
                forall |k: int| 0 <= k < N as int ==> current_arr_core@.map_values(|x: i8| x as int)[k] == current_arr_core[k as int] as int,
        {
            if current_arr_core[j] > current_arr_core[j + 1] {
                operations.push(((j + 1) as i8, (j + 2) as i8));
                let temp = current_arr_core[j];
                current_arr_core.set(j, current_arr_core[j + 1]);
                current_arr_core.set(j + 1, temp);
                swapped_in_pass = true;

                if operations.len() >= max_ops {
                    break;
                }
            }
            j = j + 1;
        }

        if !swapped_in_pass {
            break;
        }

        i = i + 1;
    }
    operations
}
// </vc-code>


}

fn main() {}