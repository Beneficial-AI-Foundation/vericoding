use vstd::prelude::*;

verus! {

// Precondition definition
spec fn remove_front_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Helper function to copy from index i onwards
fn copy_from(a: &Vec<i32>, i: usize, acc: &mut Vec<i32>)
    requires
        i <= a.len(),
        old(acc).len() + (a.len() - i) <= usize::MAX,
    ensures
        acc.len() == old(acc).len() + (a.len() - i),
        forall|j: int| 0 <= j < old(acc).len() ==> acc[j] == old(acc)[j],
        forall|j: int| old(acc).len() <= j < acc.len() ==> 
            acc[j] == a[(j - old(acc).len() + i) as int],
    decreases a.len() - i
{
    if i < a.len() {
        acc.push(a[i]);
        copy_from(a, i + 1, acc);
    }
}

// Main function
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires
        remove_front_precond(a),
    ensures
        remove_front_postcond(a, &result),
{
    let mut c = Vec::with_capacity((a.len() - 1) as usize);
    copy_from(a, 1, &mut c);
    c
}

// Postcondition definition
spec fn remove_front_postcond(a: &Vec<i32>, result: &Vec<i32>) -> bool {
    a.len() > 0 
    && result.len() == a.len() - 1 
    && (forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1])
}

} // verus!

fn main() {}