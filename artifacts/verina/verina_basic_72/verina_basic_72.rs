use vstd::prelude::*;

verus! {

// Precondition function (always true in this case)
pub open spec fn append_precond(a: Seq<int>, b: int) -> bool {
    true
}

// Helper function to copy array elements
fn copy(a: &Vec<int>, i: usize, acc: &mut Vec<int>)
    requires
        i <= a.len(),
        old(acc).len() == i,
        forall|j: int| 0 <= j < i ==> old(acc)[j] == a[j],
    ensures
        acc.len() == a.len(),
        forall|j: int| 0 <= j < a.len() ==> acc[j] == a[j],
    decreases a.len() - i,
{
    if i < a.len() {
        acc.push(a[i]);
        copy(a, i + 1, acc);
    }
}

// Main append function
pub fn append(a: &Vec<int>, b: int) -> (result: Vec<int>)
    requires
        append_precond(a@, b),
    ensures
        append_postcond(a@, b, result@),
{
    let mut c_initial = Vec::new();
    copy(a, 0, &mut c_initial);
    c_initial.push(b);
    c_initial
}

// Postcondition specification
pub open spec fn append_postcond(a: Seq<int>, b: int, result: Seq<int>) -> bool {
    (forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]) &&
    result[a.len() as int] == b &&
    result.len() == a.len() + 1
}

// Theorem equivalent (specification-level lemma)
proof fn append_spec_satisfied(a: Seq<int>, b: int, result: Seq<int>)
    requires
        append_precond(a, b),
        // Assume the result satisfies what append would produce
        (forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]) &&
        result[a.len() as int] == b &&
        result.len() == a.len() + 1,
    ensures
        append_postcond(a, b, result),
{
    // The proof is trivial since the requires clause already states
    // exactly what the postcondition requires
}

} // verus!

fn main() {
    // Empty main for compilation
}