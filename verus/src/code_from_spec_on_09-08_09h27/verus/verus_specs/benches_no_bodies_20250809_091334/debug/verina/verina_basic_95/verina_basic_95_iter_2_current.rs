use vstd::prelude::*;

verus! {

// Precondition for swap function  
spec fn swap_precond(arr: Seq<i32>, i: i32, j: i32) -> bool {
    i >= 0 &&
    j >= 0 &&
    (i as nat) < arr.len() &&
    (j as nat) < arr.len()
}

// Postcondition for swap function
spec fn swap_postcond(arr: Seq<i32>, i: i32, j: i32, result: Seq<i32>) -> bool {
    result[i as int] == arr[j as int] &&
    result[j as int] == arr[i as int] &&
    result.len() == arr.len() &&
    forall |k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k]
}

// Swap function implementation
fn swap(arr: Vec<i32>, i: i32, j: i32) -> (result: Vec<i32>)
    requires
        swap_precond(arr@, i, j),
    ensures
        swap_postcond(arr@, i, j, result@),
{
    let mut result = arr;
    /* code modified by LLM (iteration 1): store both values in temp variables before mutation to avoid borrowing conflicts */
    let temp_i = result[i as usize];
    let temp_j = result[j as usize];
    result.set(i as usize, temp_j);
    result.set(j as usize, temp_i);
    result
}

// Pure specification version of swap
spec fn swap_spec(arr: Seq<i32>, i: i32, j: i32) -> Seq<i32>
    recommends
        swap_precond(arr, i, j),
{
    arr.update(i as int, arr[j as int])
       .update(j as int, arr[i as int])
}

// Theorem proving the specification is satisfied
proof fn swap_spec_satisfied(arr: Seq<i32>, i: i32, j: i32)
    requires
        swap_precond(arr, i, j),
    ensures
        swap_postcond(arr, i, j, swap_spec(arr, i, j)),
{
    let result = swap_spec(arr, i, j);
    
    // Prove each part of the postcondition
    assert(result[i as int] == arr[j as int]);
    assert(result[j as int] == arr[i as int]);
    assert(result.len() == arr.len());
    
    // Prove that all other elements remain unchanged
    assert(forall |k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k]) by {
        assert forall |k: int| 0 <= k < arr.len() && k != i && k != j implies result[k] == arr[k] by {
            if k != i && k != j {
                assert(result[k] == arr.update(i as int, arr[j as int]).update(j as int, arr[i as int])[k]);
                assert(result[k] == arr[k]);
            }
        }
    }
}

// Test function
fn test_swap() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    
    let swapped = swap(v, 0, 3);
    assert(swapped@[0] == 4);
    assert(swapped@[3] == 1);
    assert(swapped@[1] == 2);
    assert(swapped@[2] == 3);
}

fn main() {
    test_swap();
}

} // verus!