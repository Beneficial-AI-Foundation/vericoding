use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = s.len();
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    for i in 0..n
        invariant
            prefixes.len() == i,
            forall |k: int| 0 <= k < i ==> #![trigger(prefixes@[k]@)] prefixes@[k]@ == s@.subrange(0, k + 1)
    {
        let mut prefix: Vec<u8> = Vec::new();
        for j in 0..(i + 1)
            invariant
                prefix.len() == j,
                forall |k: int| 0 <= k < j ==> #![trigger(prefix@[k])] prefix@[k] == s@[k]
        {
            prefix.push(s[j]);
        }
        // Assert the prefix is correct
        assert(prefix@ == s@.subrange(0, i + 1));
        prefixes.push(prefix);
    }
    // Assert the lengths match and the postcondition holds
    assert(prefixes.len() == s.len());
    assert(forall |i: int| 0 <= i < s.len() ==> prefixes@[i]@ == s@.subrange(0, i + 1));
    prefixes
}
// </vc-code>

fn main() {}
}