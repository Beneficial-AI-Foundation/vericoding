use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;
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
    // Backward copy to shift the suffix
    let mut i = l;
    while i > at
        invariant
            at <= i <= l,
    {
        proof {
            // Proof that indices are within bounds
            let pos = (i + p);
            assert(at + p <= pos <= l + p);
            assert(pos < old(line).len());
            assert(i < old(line).len());
        }
        line[ ((i + p) as u32) as usize ] = line[ (i as u32) as usize ];
        i = i - 1;
    }
    // Insert the new characters
    let mut j = 0;
    while j < p
        invariant
            0 <= j <= p,
            j == 0 ==> at <= old(line).len() - (l + p) + at,
    {
        proof {
            let pos = (at + j);
            assert(0 <= pos < old(line).len());
            assert(j < nl.len());
        }
        line[ ((at + j) as u32) as usize ] = nl[ (j as u32) as usize ];
        j = j + 1;
    }
}
// </vc-code>

fn main() {
}

}