use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn replace(a: &mut Vec<i32>, x: i32, y: i32)"
docstring: Implement replace functionality.
*/
// </vc-description>

// <vc-spec>
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    ensures a@.len() == old(a)@.len(),
    ensures forall|i: int| 0 <= i < a@.len() ==> 
        (if old(a)@[i] == x { a@[i] == y } else { a@[i] == old(a)@[i] })
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariants and indexing */
    let mut i = 0;
    while i < a.len()
        invariant 0 <= i <= a@.len(),
        invariant a@.len() == old(a)@.len(),
        invariant forall|j: int| 0 <= j < i ==> 
            (if old(a)@[j] == x { a@[j] == y } else { a@[j] == old(a)@[j] }),
        invariant forall|j: int| i <= j < a@.len() ==> a@[j] == old(a)@[j]
    {
        if a[i] == x {
            a.set(i, y);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}
}