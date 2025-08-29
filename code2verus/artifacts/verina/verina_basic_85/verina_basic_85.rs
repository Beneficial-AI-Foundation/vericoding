use vstd::prelude::*;

verus! {

// Precondition for reverse function
spec fn reverse_precond(a: Seq<int>) -> bool {
    true
}

// Core recursive function for reversing array  
fn reverse_core(mut arr: Vec<int>, i: usize) -> (result: Vec<int>)
    requires 
        i <= arr.len(),
    ensures
        result.len() == arr.len(),
    decreases arr.len() - i,
{
    if i < arr.len() / 2 {
        let j = arr.len() - 1 - i;
        let temp = arr[i];
        let val_j = arr[j];
        arr.set(i, val_j);
        arr.set(j, temp);
        reverse_core(arr, i + 1)
    } else {
        arr
    }
}

// Main reverse function
fn reverse(a: Vec<int>) -> (result: Vec<int>)
    requires reverse_precond(a@)
{
    reverse_core(a, 0)
}

// Postcondition for reverse function
spec fn reverse_postcond(a: Seq<int>, result: Seq<int>) -> bool {
    result.len() == a.len() && 
    (forall|i: int| 0 <= i < a.len() ==> result[i] == a[a.len() - 1 - i])
}

}

fn main() {}