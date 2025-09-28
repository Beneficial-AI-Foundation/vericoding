use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper functions / proofs (none needed for this file)
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
    // take a copy of the original contents to refer to during the proof
    let old_line = line.clone();

    // Shift the tail of length (l - at) right by p positions.
    // Iterate from i = l-1 down to at.
    let mut i: int = l - 1;
    while i >= at
        invariant 0 <= at && at <= l &&
                  0 <= i + 1 && i + 1 <= l &&
                  (forall|j: int| (0 <= j && j < at) ==> line@[(j as usize)] == old_line@[(j as usize)]) &&
                  (forall|j: int| (i + 1 <= j && j < l) ==> line@[((j + p) as usize)] == old_line@[(j as usize)]);
    {
        // i >= at >= 0, so casts to usize are safe
        let ch = old_line[(i as usize)];
        line.set(((i + p) as usize), ch);
        i -= 1;
    }

    // Now insert p characters from nl at position at
    let mut k: int = 0;
    while k < p
        invariant 0 <= k && k <= p &&
                  (forall|j: int| (0 <= j && j < k) ==> line@[((at + j) as usize)] == nl@[(j as usize)]) &&
                  0 <= at && at <= l &&
                  (forall|j: int| (0 <= j && j < at) ==> line@[(j as usize)] == old_line@[(j as usize)]) &&
                  (forall|j: int| (at <= j && j < l) ==> line@[((j + p) as usize)] == old_line@[(j as usize)]);
    {
        let ch = nl[(k as usize)];
        line.set(((at + k) as usize), ch);
        k += 1;
    }

    // proofs to show final postconditions

    // 1) inserted elements
    proof {
        assert((forall|i: int| (0 <= i && i < p) ==> line@[((at + i) as usize)] == nl@[(i as usize)]));
    }

    // 2) elements before at unchanged
    proof {
        assert((forall|i: int| (0 <= i && i < at) ==> line@[(i as usize)] == old_line@[(i as usize)]));
    }

    // 3) tail shifted correctly: for i in [at+p, l+p) line[i] == old_line[i - p]
    proof {
        assert((forall|i: int| (at + p <= i && i < l + p) ==> line@[(i as usize)] == old_line@[((i - p) as usize)]));
    }
}
// </vc-code>

fn main() {
}

}