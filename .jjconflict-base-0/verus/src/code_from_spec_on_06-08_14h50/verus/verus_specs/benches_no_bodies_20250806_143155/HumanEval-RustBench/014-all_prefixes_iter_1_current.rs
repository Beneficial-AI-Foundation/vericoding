use vstd::prelude::*;

verus! {

fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)
    // post-conditions-start
    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
    // post-conditions-end
{
    let mut prefixes = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
    {
        let mut prefix = Vec::new();
        let mut k = 0;
        
        while k <= i
            invariant
                prefix.len() == k,
                forall|l: int| #![auto] 0 <= l < k ==> prefix[l] == s[l],
        {
            prefix.push(s[k]);
            k += 1;
        }
        
        prefixes.push(prefix);
        i += 1;
    }
    
    prefixes
}

}
fn main() {}