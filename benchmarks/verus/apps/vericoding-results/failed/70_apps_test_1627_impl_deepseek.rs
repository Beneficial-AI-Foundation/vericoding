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
/* helper modified by LLM (iteration 5): Fixed sequence conversion syntax in swap_adjacent proof */

proof fn lemma_swap_adjacent_preserves_length(arr: Seq<int>, i: int, j: int)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
        j == i + 1,
    ensures
        swap_adjacent(arr, i, j).len() == arr.len(),
{
}

proof fn lemma_apply_operations_preserves_length(arr: Seq<int>, operations: Seq<(int, int)>)
    ensures
        apply_operations(arr, operations).len() == arr.len(),
    decreases operations.len(),
{
    if operations.len() == 0 {
    } else {
        let op = operations[0];
        if 1 <= op.0 <= arr.len() && 1 <= op.1 <= arr.len() && op.1 == op.0 + 1 {
            lemma_swap_adjacent_preserves_length(arr, (op.0 - 1) as int, (op.1 - 1) as int);
            lemma_apply_operations_preserves_length(swap_adjacent(arr, (op.0 - 1) as int, (op.1 - 1) as int), operations.drop_first());
        } else {
            lemma_apply_operations_preserves_length(arr, operations.drop_first());
        }
    }
}

proof fn lemma_sorted_implies_zero_operations_needed(arr: Seq<int>)
    requires
        is_sorted(arr),
    ensures
        forall |operations: Seq<(int, int)>| apply_operations(arr, operations) == arr,
    decreases arr.len(),
{
    if arr.len() <= 1 {
    } else {
        lemma_sorted_implies_zero_operations_needed(arr.drop_last());
    }
}

fn bubble_sort_step(arr: &mut Vec<i8>, i: usize) -> (swapped: bool)
    requires
        old(arr)@.len() >= 1,
        0 <= i < old(arr)@.len() - 1,
    ensures
        arr@.len() == old(arr)@.len(),
        if old(arr)@[i] as int > old(arr)@[i + 1] as int {
            arr@ == swap_adjacent(old(arr)@, i as int, (i + 1) as int),
            swapped == true
        } else {
            arr@ == old(arr)@,
            swapped == false
        },
{
    if arr[i] > arr[i + 1] {
        let temp = arr[i];
        arr[i] = arr[i + 1];
        arr[i + 1] = temp;
        true
    } else {
        false
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
    /* code modified by LLM (iteration 5): Fixed sequence conversion syntax in ensures clause */
    let mut operations = Vec::new();
    let mut current_arr = arr.clone();
    
    proof {
        lemma_apply_operations_preserves_length(arr@, operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)));
    }
    
    if is_sorted(arr@.map_values(|x: i8| x as int)) {
        return operations;
    }
    
    let mut sorted = false;
    let max_operations = 20000;
    
    while !sorted && operations.len() < max_operations 
        invariant
            operations@.len() <= max_operations,
            current_arr@.len() == arr@.len(),
            valid_operations(operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int)), n as int),
            current_arr@.map_values(|x: i8| x as int) == apply_operations(arr@.map_values(|x: i8| x as int), operations@.map_values(|op: (i8, i8)| (op.0 as int, op.1 as int))),
        decreases max_operations - operations.len(),
    {
        sorted = true;
        
        for i in 0..(n - 1) as usize {
            if current_arr[i] > current_arr[i + 1] {
                let swapped = bubble_sort_step(&mut current_arr, i);
                if swapped {
                    operations.push(((i + 1) as i8, (i + 2) as i8));
                    sorted = false;
                }
            }
            
            if operations.len() >= max_operations {
                break;
            }
        }
    }
    
    operations
}
// </vc-code>


}

fn main() {}