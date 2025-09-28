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
fn is_sorted_vec(arr: &Vec<i8>) -> bool {
    let n = arr.len();
    if n <= 1 {
        true
    } else {
        for i in 0..n-1 {
            if arr[i] > arr[i+1] {
                return false;
            }
        }
        true
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
/* code modified by LLM (iteration 4): fixed swap by using manual swap with temporary variable */
{
    let n_usize = n as usize;
    if is_sorted_vec(&arr) {
        return Vec::new();
    }

    let ghost arr_orig = arr@;
    let mut arr_mut = arr.clone();
    let mut operations: Vec<(i8, i8)> = Vec::new();
    let mut count = 0;
    let mut swapped = true;

    while swapped && count < 20000
        invariant
            operations.len() == count,
            count <= 20000,
            arr_mut@.map_values(|x: i8| x as int) == apply_operations(
                arr_orig.map_values(|x: i8| x as int),
                operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))
            ),
    {
        swapped = false;
        for i in 0..n_usize-1
            invariant
                arr_mut@.map_values(|x: i8| x as int) == apply_operations(
                    arr_orig.map_values(|x: i8| x as int),
                    operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))
                ),
                operations.len() == count,
                count <= 20000,
        {
            if arr_mut[i] > arr_mut[i+1] {
                let op = (i as i8 + 1, i as i8 + 2);
                // Manual swap
                let temp = arr_mut[i];
                arr_mut[i] = arr_mut[i+1];
                arr_mut[i+1] = temp;
                operations.push(op);
                count += 1;
                swapped = true;
                if count == 20000 {
                    break;
                }
            }
        }
    }

    operations
}
// </vc-code>


}

fn main() {}