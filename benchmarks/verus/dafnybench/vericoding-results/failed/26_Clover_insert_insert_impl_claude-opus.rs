use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    // We need to shift elements to the right to make room for the new characters
    // First, we'll resize the vector to accommodate the new elements
    let old_len = line.len();
    
    // Extend the vector with p placeholder elements
    let mut j: usize = 0;
    while j < p as usize
        invariant
            0 <= j <= p,
            j as int <= p,
            line.len() == old_len + j,
            forall|i: int| (0 <= i < old_len as int) ==> line@[i] == old(line)@[i],
    {
        line.push(' '); // placeholder character
        j = j + 1;
    }
    
    // Now shift elements from position 'at' to 'l-1' to the right by p positions
    // We work backwards to avoid overwriting
    let mut i: usize = l as usize;
    while i > at as usize
        invariant
            at <= i as int <= l,
            line.len() == old_len + p as usize,
            forall|k: int| (0 <= k < at) ==> line@[k] == old(line)@[k],
            forall|k: int| (i as int <= k < l) ==> line@[k + p] == old(line)@[k],
            forall|k: int| (at <= k < i as int) ==> line@[k] == old(line)@[k],
    {
        i = i - 1;
        line.set(i + p as usize, line@[i as int]);
        
        assert(forall|k: int| (0 <= k < at) ==> line@[k] == old(line)@[k]);
        assert(forall|k: int| (i as int <= k < l) ==> line@[k + p] == old(line)@[k]);
    }
    
    // Now insert the new characters at position 'at'
    let mut k: usize = 0;
    while k < p as usize
        invariant
            0 <= k <= p,
            k as int <= p,
            line.len() == old_len + p as usize,
            forall|j: int| (0 <= j < k as int) ==> line@[at + j] == nl@[j],
            forall|j: int| (0 <= j < at) ==> line@[j] == old(line)@[j],
            forall|j: int| (at + p <= j < l + p) ==> line@[j] == old(line)@[j - p],
    {
        line.set(at as usize + k, nl@[k as int]);
        k = k + 1;
    }
    
    assert(forall|i: int| (0 <= i < p) ==> line@[at + i] == nl@[i]);
    assert(forall|i: int| (0 <= i < at) ==> line@[i] == old(line)@[i]);
    assert(forall|i: int| (at + p <= i < l + p) ==> line@[i] == old(line)@[i - p]);
}
// </vc-code>

fn main() {
}

}