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
    /* code modified by LLM (iteration 3): fixed type mismatch in invariant by removing unnecessary casts */
    let mut result = Vec::new();
    let mut index: usize = 0;

    while index < str1.len() && index < str2.len() && str1[index] == str2[index]
        invariant
            result.len() == index,
            forall|i: int| 0 <= i < (index as int) ==> 
                result[i] == str1[i] && result[i] == str2[i],
            index as int <= str1.len() as int,
            index as int <= str2.len() as int,
        decreases (str1.len() as int - index as int) + (str2.len() as int - index as int)
    {
        result.push(str1[index]);
        index = index + 1;
    }

    result
}
// </vc-code>

}
fn main() {}