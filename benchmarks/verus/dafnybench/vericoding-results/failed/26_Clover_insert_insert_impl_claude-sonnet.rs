use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert(line: &mut Vec<char>, l: int, nl: &Vec<char>, p: int, at: int)
    requires 
        0 <= l + p <= old(line).len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
    ensures 
        forall|i: int| (0 <= i < p) ==> line[at + i] == nl[i],
        forall|i: int| (0 <= i < at) ==> line[i] == old(line)[i],
        forall|i: int| (at + p <= i < l + p) ==> line[i] == old(line)[i - p],
// </vc-spec>
// <vc-code>
{
    let old_line = Ghost(*line);
    
    // First, we need to make space by moving existing elements to the right
    // We'll work backwards to avoid overwriting data we need to move
    let mut i = l - 1;
    while i >= at
        invariant
            0 <= at <= l,
            at - 1 <= i < l,
            0 <= l + p <= line.len(),
            0 <= p <= nl.len(),
            // Elements that have been moved are correct
            forall|j: int| (i + 1 <= j < l) ==> line@[j + p] == old_line@[j],
            // Elements before at are unchanged
            forall|j: int| (0 <= j < at) ==> line@[j] == old_line@[j],
            // Elements between at and i+1 are still in original positions
            forall|j: int| (at <= j <= i) ==> line@[j] == old_line@[j],
    {
        line.set((i + p) as usize, line@[i]);
        i = i - 1;
    }
    
    // Now insert the new characters from nl
    let mut j = 0;
    while j < p
        invariant
            0 <= j <= p,
            0 <= p <= nl.len(),
            0 <= at <= l,
            0 <= l + p <= line.len(),
            // Characters we've inserted so far are correct
            forall|k: int| (0 <= k < j) ==> line@[at + k] == nl@[k],
            // Characters before at are unchanged
            forall|k: int| (0 <= k < at) ==> line@[k] == old_line@[k],
            // Characters that were shifted are correct
            forall|k: int| (at + p <= k < l + p) ==> line@[k] == old_line@[k - p],
    {
        line.set((at + j) as usize, nl@[j]);
        j = j + 1;
    }
}
// </vc-code>

fn main() {
}

}