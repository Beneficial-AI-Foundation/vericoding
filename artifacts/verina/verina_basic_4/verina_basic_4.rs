use vstd::prelude::*;

verus! {

// Precondition: k must be between 1 and the array size (inclusive)
spec fn kth_element_precond(arr: Seq<i32>, k: nat) -> bool {
    k >= 1 && k <= arr.len()
}

// The main function that returns the k-th element (1-indexed)  
fn kth_element(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires 
        kth_element_precond(arr@, k as nat),
    ensures
        kth_element_postcond(arr@, k as nat, result as int),
{
    arr[k - 1]
}

// Postcondition: there exists an element in the array that equals the result
// and the result equals the k-th element (matching Lean's any predicate)
spec fn kth_element_postcond(arr: Seq<i32>, k: nat, result: int) -> bool {
    exists|i: int| 0 <= i < arr.len() && 
        #[trigger] arr[i] == result && 
        result == arr[k as int - 1] as int
}

// Proof that demonstrates the specification is satisfied
proof fn kth_element_spec_satisfied(arr: Seq<i32>, k: nat) 
    requires 
        kth_element_precond(arr, k),
    ensures 
        kth_element_postcond(arr, k, arr[k as int - 1] as int),
{
    // The witness is the element at position k-1 itself
    assert(0 <= k as int - 1 < arr.len()) by {
        assert(k >= 1 && k <= arr.len());
        assert(k as int >= 1);
        assert(k as int - 1 >= 0);
        assert(k as int <= arr.len());
        assert(k as int - 1 < arr.len());
    };
    
    // The element at k-1 satisfies both conditions
    let witness_idx = k as int - 1;
    assert(arr[witness_idx] as int == arr[k as int - 1] as int);
}

} // verus!

fn main() {
    // Test the function
    let arr = vec![10, 20, 30, 40, 50];
    let third_element = kth_element(&arr, 3); // Should return 30
    println!("3rd element: {}", third_element);
}