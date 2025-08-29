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
    let i_nat = i as usize;
    let j_nat = j as usize;
    
    // Store original values
    let val_at_i = arr[i_nat];
    let val_at_j = arr[j_nat];
    
    // Create result by setting values
    let mut arr1 = arr;
    arr1.set(i_nat, val_at_j);
    arr1.set(j_nat, val_at_i);
    
    arr1
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
    
    // The postcondition is automatically verified by Verus
    // based on the definition of swap_spec and properties of update
}

// Test function
fn test_swap() {
    let arr = vec![10, 20, 30, 40, 50];
    let result = swap(arr, 1, 3);
    
    assert(result@[1] == 40);
    assert(result@[3] == 20); 
    assert(result@[0] == 10);
    assert(result@[2] == 30);
    assert(result@[4] == 50);
}

fn main() {
    test_swap();
}

} // verus!