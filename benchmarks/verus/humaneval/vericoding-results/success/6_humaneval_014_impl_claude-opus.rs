// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_prefixes(s: Seq<char>, result: Seq<Seq<char>>) -> bool {
    result.len() == s.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == s.subrange(0, i + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures valid_prefixes(s@, result@.map(|i, v: Vec<char>| v@))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i
    {
        let mut prefix: Vec<char> = Vec::new();
        let mut j: usize = 0;
        
        while j <= i
            invariant
                j <= i + 1,
                i < s.len(),
                prefix.len() == j,
                prefix@ == s@.subrange(0, j as int),
            decreases i + 1 - j
        {
            prefix.push(s[j]);
            j = j + 1;
        }
        
        assert(prefix@ == s@.subrange(0, (i + 1) as int));
        result.push(prefix);
        i = i + 1;
    }
    
    assert(result.len() == s.len());
    assert(forall|k: int| 0 <= k < result.len() ==> result@[k]@ == s@.subrange(0, k + 1));
    
    result
}
// </vc-code>


}

fn main() {}