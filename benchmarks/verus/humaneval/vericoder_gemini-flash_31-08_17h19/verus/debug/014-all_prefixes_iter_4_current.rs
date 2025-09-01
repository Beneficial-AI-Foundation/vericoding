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
        v.push(s[i as usize]);
        proof {
            assert(i-start < v.len()); // This assertion is likely redundant because v.push() ensures the length
            assert(i < s.len()); // This assertion is redundant because the while loop condition ensures i < end and end <= s.len()
            
            // The purpose of this `set_tracked_vec_index` was probably to prove the relationship
            // between the content of `v` and `s`. 
            // The `v@ == s@.subrange(start, i)` invariant handles this,
            // and the `push` operation implicitly extends this proven property.
            // Explicitly setting a tracked index is usually for when you mutate an existing index,
            // not when you append. If `set_tracked_vec_index` is needed for `push`, 
            // it implies `push` doesn't fully update the track_vec proof.
            // However, typical Verus Vector usage with `push` is usually sufficiently verified by its own logic.
            // If the original intention was to directly manipulate the ghost state after push,
            // this is technically not the right way to use `set_tracked_vec_index`.
            // Let's remove the problematic line and see if the invariant holds which it should.
            // v.set_tracked_vec_index(i - start, s.tracked_vec_get(i as usize)); 
        }
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