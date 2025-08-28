use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn as_usize_spec(x: int) -> usize
    requires 0 <= x < usize::MAX
{
    x as usize
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let old_line = line.clone();
    
    // First, we need to make space for the new characters
    // Resize the vector to accommodate the insertion
    line.resize(as_usize_spec(l + p), ' ');
    
    // Move existing characters after insertion point to make room
    let mut i = l - 1;
    while i >= at
        invariant
            0 <= at <= l,
            at - 1 <= i < l,
            line.len() == as_usize_spec(l + p),
            forall|j: int| (i + 1 <= j < l) ==> line@[j + p] == old_line@[j],
            forall|j: int| (0 <= j < at) ==> line@[j] == old_line@[j],
        decreases i - at + 1
    {
        line.set(as_usize_spec(i + p), line[as_usize_spec(i)]);
        if i == at {
            break;
        }
        i = i - 1;
    }
    
    // Insert the new characters
    let mut j = 0;
    while j < p
        invariant
            0 <= j <= p,
            0 <= p <= nl.len(),
            0 <= at <= l,
            line.len() == as_usize_spec(l + p),
            forall|k: int| (0 <= k < j) ==> line@[at + k] == nl@[k],
            forall|k: int| (0 <= k < at) ==> line@[k] == old_line@[k],
            forall|k: int| (at + p <= k < l + p) ==> line@[k] == old_line@[k - p],
        decreases p - j
    {
        line.set(as_usize_spec(at + j), nl[as_usize_spec(j)]);
        j = j + 1;
    }
}
// </vc-code>

fn main() {
}

}