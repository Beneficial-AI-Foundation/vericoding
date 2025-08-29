use vstd::prelude::*;

verus! {

// Precondition: array size must be greater than 0
spec fn is_greater_precond(n: int, a: Seq<int>) -> bool {
    a.len() > 0
}

// Main function: check if n is greater than all elements in array
// This implements the logic of Array.all (fun x => n > x)
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0
    ensures result <==> (forall|i: int| 0 <= i < a.len() ==> n > a[i])
{
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a[j as int]
        decreases a.len() - i
    {
        if n <= a[i] {
            return false;
        }
        i += 1;
    }
    true
}

// Postcondition specification - matches the Lean postcondition exactly
spec fn is_greater_postcond(n: int, a: Seq<int>, result: bool) -> bool {
    (forall|i: int| 0 <= i < a.len() ==> n > a[i]) <==> result
}

// Specification version that matches the implementation
spec fn spec_is_greater(n: int, a: Seq<int>) -> bool
    recommends a.len() > 0
{
    forall|i: int| 0 <= i < a.len() ==> n > a[i]
}

// Proof that the function satisfies its specification
proof fn is_greater_spec_satisfied(n: int, a: Seq<int>)
    requires is_greater_precond(n, a)
    ensures is_greater_postcond(n, a, spec_is_greater(n, a))
{
    // The postcondition is satisfied by the definition of spec_is_greater
    // and the ensures clause of is_greater
}

}

fn main() {}