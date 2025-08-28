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
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i
    {
        let mut prefix: Vec<u8> = Vec::new();
        let mut k = 0;
        
        while k <= i
            invariant
                k <= i + 1,
                i < s.len(),
                prefix.len() == k,
                forall|m: int| #![auto] 0 <= m < k ==> prefix[m] == s[m],
            decreases i + 1 - k
        {
            prefix.push(s[k]);
            k += 1;
        }
        
        prefixes.push(prefix);
        i += 1;
    }
    
    prefixes
}
// </vc-code>

}
fn main() {}