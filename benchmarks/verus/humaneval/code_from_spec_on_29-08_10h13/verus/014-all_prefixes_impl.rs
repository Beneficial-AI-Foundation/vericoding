use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma fn lemma_subrange_len(s: Seq<u8>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures s.subrange(start, end).len() == end - start
{
}

lemma fn lemma_prefix_construction(s: &Vec<u8>, i: usize, prefix: &Vec<u8>)
    requires 
        i < s.len(),
        prefix.len() == (i + 1) as nat,
        forall|m: int| #![auto] 0 <= m <= i ==> prefix[m] == s[m]
    ensures prefix@ == s@.subrange(0, (i + 1) as int)
{
    assert(prefix@.len() == (i + 1) as nat);
    assert(s@.subrange(0, (i + 1) as int).len() == (i + 1) as nat) by {
        lemma_subrange_len(s@, 0, (i + 1) as int);
    }
    
    assert forall|j: int| #![auto] 0 <= j < (i + 1) as int ==> prefix@[j] == s@.subrange(0, (i + 1) as int)[j] by {
        assert(prefix@[j] == s@[j]);
        assert(s@.subrange(0, (i + 1) as int)[j] == s@[j]);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def all_prefixes(string: str) -> List[str]"
docstring: |
Return list of all prefixes from shortest to longest of the input string
test_cases:
- input: "abc"
expected_output:
- "a"
- "ab"
- "abc"
*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): fixed lemma syntax from lemma_by to lemma */
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i
    {
        let mut prefix = Vec::new();
        let mut k = 0;
        
        while k < i + 1
            invariant
                0 <= k <= i + 1,
                k <= s.len(),
                prefix.len() == k,
                forall|m: int| #![auto] 0 <= m < k ==> prefix[m] == s[m],
            decreases i + 1 - k
        {
            prefix.push(s[k]);
            k += 1;
        }
        
        proof {
            lemma_prefix_construction(s, i, &prefix);
        }
        
        prefixes.push(prefix);
        i += 1;
    }
    
    prefixes
}
// </vc-code>

}
fn main() {}