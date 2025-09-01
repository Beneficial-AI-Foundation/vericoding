use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>
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
    for i in 0..s.len()
        invariant
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j+1),
    {
        let end = i + 1;
        let mut prefix = Vec::new();
        for j in 0..end
            invariant
                prefix.len() == j,
                prefix@ == s@.subrange(0, j as int),
        {
            prefix.push(s[j]);
        }
        prefixes.push(prefix);
    }
    prefixes
}
// </vc-code>

fn main() {}
}