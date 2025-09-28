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
    let ghost old_line = line@;

    // Shift the segment [at, l) to the right by p positions
    let mut i: int = l - 1;
    while i >= at
        invariant 0 <= at <= l
        invariant 0 <= p <= nl.len()
        invariant l + p <= old_line.len()
        invariant -1 <= i < l
        invariant forall|k: int|
            (i + 1 <= k && k < l) ==> #[trigger] line[k + p] == old_line[k]
        invariant forall|k: int|
            (0 <= k && k <= i) ==> #[trigger] line[k] == old_line[k]
    {
        let v = line[i as usize];
        line[(i + p) as usize] = v;
        i -= 1;
    }

    // Insert the first p characters of nl at position at
    let mut j: int = 0;
    while j < p
        invariant 0 <= j <= p
        invariant 0 <= at <= l
        invariant 0 <= p <= nl.len()
        invariant l + p <= old_line.len()
        invariant forall|k: int|
            (at <= k && k < l) ==> #[trigger] line[k + p] == old_line[k]
        invariant forall|t: int|
            (0 <= t && t < j) ==> #[trigger] line[at + t] == nl[t]
        invariant forall|k: int|
            (0 <= k && k < at) ==> #[trigger] line[k] == old_line[k]
    {
        let v = nl[j as usize];
        line[(at + j) as usize] = v;
        j += 1;
    }
}
// </vc-code>

fn main() {
}

}