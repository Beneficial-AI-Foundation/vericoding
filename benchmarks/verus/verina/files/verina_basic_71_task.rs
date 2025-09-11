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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}