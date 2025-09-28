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
/* helper modified by LLM (iteration 2): simple bounds lemma for adjacent operation indices */
fn op_valid_after_index(n: int, i: int)
    requires
        1 <= n,
        0 <= i && i + 1 < n,
    ensures
        1 <= i + 1 && i + 2 <= n,
{
    proof {
        assert(i + 1 >= 1);
        assert(i + 2 <= n);
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
{
    /* code modified by LLM (iteration 2): avoid complex expression in swap by using a temporary index */
    let mut operations: Vec<(i8, i8)> = Vec::new();
    let n_usize: usize = n as usize;
    if n_usize <= 1 {
        return operations;
    }
    let mut arr = arr;
    let mut limit: usize = n_usize - 1;
    let mut remaining: i64 = 20000;
    let mut i: usize = 0;
    let mut pass_swapped: bool = false;
    let mut sorted_flag: bool = false;

    while remaining > 0 && !sorted_flag
        invariant
            0 <= remaining as int && remaining as int <= 20000,
            valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int),
            0 <= i as int && i as int <= limit as int,
    decreases remaining as int
    {
        if i >= limit {
            if !pass_swapped {
                sorted_flag = true;
            } else {
                i = 0;
                pass_swapped = false;
            }
        } else {
            if arr[i] > arr[i + 1] {
                let j = i + 1;
                arr.swap(i, j);
                let op0 = i as i8 + 1;
                let op1 = i as i8 + 2;
                operations.push((op0, op1));
                proof {
                    op_valid_after_index(n as int, i as int);
                }
                pass_swapped = true;
            }
            i += 1;
            remaining -= 1;
        }
    }

    operations
}
// </vc-code>


}

fn main() {}