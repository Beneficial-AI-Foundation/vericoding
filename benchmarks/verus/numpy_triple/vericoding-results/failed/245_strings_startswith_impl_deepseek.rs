// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}
// </vc-preamble>

// <vc-helpers>


spec fn lemma_string_starts_with_properties(s: Seq<char>, prefix: Seq<char>) 
    ensures 
        string_starts_with(s, prefix) == (
            prefix.len() <= s.len() 
            && s.subrange(0, prefix.len()) == prefix
        ),
        string_starts_with(s, prefix) ==> prefix.len() <= s.len(),
        string_starts_with(s, prefix) ==> s.subrange(0, prefix.len()) == prefix,
        !string_starts_with(s, prefix) ==> (
            prefix.len() > s.len() 
            || s.subrange(0, prefix.len()) != prefix
        )
{
}

proof fn lemma_vec_index_properties<T>(v: Vec<T>, i: int) 
    requires 
        0 <= i < v.len()
    ensures 
        v[i as usize] == v@[i],
        v@.len() == v.len() as nat
{
}

/* helper modified by LLM (iteration 5): Fixed parameter type to use int for consistency with vector indexing requirements */

// </vc-helpers>

// <vc-spec>
fn startswith(a: Vec<String>, prefixes: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == prefixes.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == string_starts_with(a[i]@, prefixes[i]@))
            &&& (result[i] ==> prefixes[i]@.len() <= a[i]@.len())
            &&& (result[i] ==> a[i]@.subrange(0, prefixes[i]@.len() as int) == prefixes[i]@)
            &&& (!result[i] ==> (prefixes[i]@.len() > a[i]@.len() || a[i]@.subrange(0, prefixes[i]@.len() as int) != prefixes[i]@))
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting issues and vector indexing */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> {
                &&& (result[j as usize] == string_starts_with(a[j as usize]@, prefixes[j as usize]@))
                &&& (result[j as usize] ==> prefixes[j as usize]@.len() <= a[j as usize]@.len())
                &&& (result[j as usize] ==> a[j as usize]@.subrange(0, prefixes[j as usize]@.len()) == prefixes[j as usize]@)
                &&& (!result[j as usize] ==> (prefixes[j as usize]@.len() > a[j as usize]@.len() || a[j as usize]@.subrange(0, prefixes[j as usize]@.len()) != prefixes[j as usize]@))
            }
        decreases (a.len() - i)
    {
        proof {
            lemma_vec_index_properties(a, i as int);
            lemma_vec_index_properties(prefixes, i as int);
            lemma_string_starts_with_properties(a[i]@, prefixes[i]@);
        }
        
        let s_chars = a[i].to_string()@;
        let prefix_chars = prefixes[i].to_string()@;
        let starts_with = string_starts_with(s_chars, prefix_chars);
        result.push(starts_with);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}