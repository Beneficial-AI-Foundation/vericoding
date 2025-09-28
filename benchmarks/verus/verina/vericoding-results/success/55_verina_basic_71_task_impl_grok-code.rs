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
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len() && i < str2.len() && str1[i] == str2[i]
        invariant
            i <= str1@.len(),
            i <= str2@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> str1@[j] == result@[j] && str2@[j] == result@[j],
        decreases
            (str1@.len() as int - i as int) + (str2@.len() as int - i as int)
    {
        result.push(str1[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}