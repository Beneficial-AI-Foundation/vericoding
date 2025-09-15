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
/* code modified by LLM (iteration 3): added a decreases clause to the while loop to prove termination */
{
    let mut i: usize = 0;
    while i < str1.len() && i < str2.len() && str1[i] == str2[i]
        invariant
            i <= str1.len(),
            i <= str2.len(),
            forall|j: int| 0 <= j < i ==> str1[j] == str2[j],
        decreases str1.len() - i,
    {
        i = i + 1;
    }
    let mut result = str1.clone();
    result.truncate(i);
    result
}
// </vc-code>

}
fn main() {}