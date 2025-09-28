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
    /* code modified by LLM (iteration 4): fixed bounds and overflow issues */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i
    {
        let mut prefix: Vec<char> = Vec::new();
        let mut k = 0;
        
        while k < i + 1
            invariant
                k <= i + 1,
                prefix.len() == k,
                forall|m: int| 0 <= m < k ==> prefix@[m] == s@[m],
                i < s.len(),
            decreases i + 1 - k
        {
            prefix.push(s[k]);
            k += 1;
        }
        
        result.push(prefix);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}