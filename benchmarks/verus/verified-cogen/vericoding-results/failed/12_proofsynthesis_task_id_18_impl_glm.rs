// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_char(seq: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == c
}
// </vc-helpers>

// <vc-spec>
fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..str1.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> (str1@.contains(#[trigger] result[k]) && !str2@.contains(#[trigger] result[k])),
            forall|k: int| 0 <= k < i ==> (str2@.contains(#[trigger] str1[k]) || result@.contains(#[trigger] str1[k])),
    {
        let c = str1[i];
        
        let mut in_str2 = false;
        for j in 0..str2.len()
            invariant 
                in_str2 ==> exists|k: int| 0 <= k < j && str2@[k] == c,
                !in_str2 ==> forall|k: int| 0 <= k < j ==> str2@[k] != c,
        {
            if str2[j] == c {
                in_str2 = true;
                break;
            }
        }
        
        if !in_str2 {
            result.push(c);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}