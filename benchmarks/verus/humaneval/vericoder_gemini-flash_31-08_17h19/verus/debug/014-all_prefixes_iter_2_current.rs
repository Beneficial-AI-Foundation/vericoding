use vstd::prelude::*;

verus! {

// <vc-helpers>
fn subrange_vec(s: &Vec<u8>, start: int, end: int) -> Vec<u8>
    requires
        0 <= start <= end <= s.len(),
    ensures
        subrange_vec(s, start, end).len() == end - start,
        subrange_vec(s, start, end)@ == s@.subrange(start, end),
{
    let mut v = Vec::new();
    let mut i: int = start;
    while i < end
        invariant
            start <= i <= end,
            v.len() == i - start,
            v@ == s@.subrange(start, i),
    {
        v.push(s.tracked_vec_byte_get(i as usize));
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)
    // post-conditions-start
    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: int = 0;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
    {
        let new_prefix = subrange_vec(s, 0, i + 1);
        prefixes.push(new_prefix);
        i = i + 1;
    }
    prefixes
}
// </vc-code>

fn main() {}
}