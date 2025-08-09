Let me analyze the postcondition: it requires that there exists an element in the array that equals the result AND the result equals the k-th element. This is essentially saying the result is the k-th element of the array.

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
    // The witness for the existential is the index k-1
    assert(0 <= k as int - 1 < arr.len());
    assert(arr[k as int - 1] == arr[k as int - 1] as int);
}

} // verus!

fn main() {
    let arr = vec![10, 20, 30, 40, 50];
    let result = kth_element(&arr, 3);
    println!("The 3rd element is: {}", result);
}