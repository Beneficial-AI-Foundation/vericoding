use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
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
    let mut idx: usize = 0;
    while idx < s.len() 
        invariant
            prefixes.len() == idx,
            forall|i: int| 0 <= i < idx as int ==> prefixes@[i]@ == s@.subrange(0, i + 1),
            idx <= s.len(),
    {
        let mut prefix: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j <= idx 
            invariant
                prefix.len() == j,
                forall|m: int| 0 <= m < j as int ==> prefix@[m] == s@[m],
                j <= idx + 1,
        {
            proof {
                assert(0 <= j as int < s@.len());
            }
            prefix.push(s@[j]);
            j += 1;
        }
        proof {
            assert(prefix@.len() == idx + 1);
            assert(forall|m: int| 0 <= m <= idx ==> prefix@[m] == s@[m]);
            assert(prefix@ == s@.subrange(0, idx as int + 1 as int));
        }
        prefixes.push(prefix);
        idx += 1;
    }
    prefixes
}
// </vc-code>

fn main() {}
}