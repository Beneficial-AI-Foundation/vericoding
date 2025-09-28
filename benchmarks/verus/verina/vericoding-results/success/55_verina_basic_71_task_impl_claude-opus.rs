// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn longest_common_prefix(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() <= str1.len(),
        result.len() <= str2.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == str1[i] && result[i] == str2[i],
        result.len() == str1.len() || result.len() == str2.len() || 
            (result.len() < str1.len() && result.len() < str2.len() && str1[result.len() as int] != str2[result.len() as int]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added assertion to prove termination condition meets postcondition */
    let mut prefix = Vec::new();
    let mut i: usize = 0;
    
    while i < str1.len() && i < str2.len() && str1[i] == str2[i]
        invariant
            i <= str1.len(),
            i <= str2.len(),
            prefix.len() == i,
            forall|j: int| 0 <= j < i ==> prefix[j] == str1[j] && prefix[j] == str2[j],
        decreases str1.len() - i
    {
        prefix.push(str1[i]);
        i = i + 1;
    }
    
    // After loop: i == str1.len() || i == str2.len() || (i < str1.len() && i < str2.len() && str1[i] != str2[i])
    assert(prefix.len() == i);
    assert(i == str1.len() || i == str2.len() || (i < str1.len() && i < str2.len() && str1[i as int] != str2[i as int]));
    assert(prefix.len() == str1.len() || prefix.len() == str2.len() || 
        (prefix.len() < str1.len() && prefix.len() < str2.len() && str1[prefix.len() as int] != str2[prefix.len() as int]));
    
    prefix
}
// </vc-code>

}
fn main() {}