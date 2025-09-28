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
    /* code modified by LLM (iteration 5): Fixed cast syntax with parentheses */
    let mut operations = Vec::new();
    let mut arr_copy = arr.clone();
    let n_usize = n as usize;
    
    // Early return if already sorted or n == 1
    if n_usize <= 1 {
        return operations;
    }
    
    let mut sorted = false;
    
    while !sorted && operations.len() < 20000
        invariant
            operations.len() <= 20000,
            valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int),
            arr_copy@.len() == n_usize,
            arr_copy@ == apply_operations(arr@.map_values(|x: i8| x as int), operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))).map_values(|x: int| x as i8),
        decreases 20000 - operations.len()
    {
        sorted = true;
        let mut i: usize = 0;
        
        while i < n_usize - 1
            invariant_except_break
                i <= n_usize - 1,
                operations.len() <= 20000,
                valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int),
                arr_copy@.len() == n_usize,
                arr_copy@ == apply_operations(arr@.map_values(|x: i8| x as int), operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))).map_values(|x: int| x as i8),
            ensures
                operations.len() <= 20000,
                valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int),
                arr_copy@.len() == n_usize,
                arr_copy@ == apply_operations(arr@.map_values(|x: i8| x as int), operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))).map_values(|x: int| x as i8),
            decreases n_usize - 1 - i
        {
            if arr_copy[i] > arr_copy[i + 1] {
                // Swap adjacent elements
                let temp = arr_copy[i];
                arr_copy.set(i, arr_copy[i + 1]);
                arr_copy.set(i + 1, temp);
                
                // Record the operation (1-indexed)
                assert(i + 1 < 128 && i + 2 < 128); // i8 bounds
                let op = ((#[verifier::truncate] ((i + 1) as i8)), (#[verifier::truncate] ((i + 2) as i8)));
                operations.push(op);
                
                sorted = false;
                
                if operations.len() >= 20000 {
                    break;
                }
            }
            i = i + 1;
        }
    }
    
    operations
}
// </vc-code>


}

fn main() {}