use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i,
    {
        let mut prefix: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        
        while j <= i
            invariant
                j <= i + 1,
                i < s.len(),
                prefix.len() == j,
                prefix@ == s@.subrange(0, j as int),
            decreases i + 1 - j,
        {
            prefix.push(s[j]);
            j = j + 1;
        }
        
        assert(prefix@ == s@.subrange(0, (i + 1) as int));
        prefixes.push(prefix);
        i = i + 1;
    }
    
    prefixes
}
// </vc-code>

fn main() {}
}