// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove external_body bypass, implement actual comparison */
fn string_less_equal_impl(s1: &String, s2: &String) -> (result: bool)
    ensures result == string_le(s1@, s2@)
{
    let bytes1 = s1.as_bytes();
    let bytes2 = s2.as_bytes();
    let mut i: usize = 0;
    let len1 = bytes1.len();
    let len2 = bytes2.len();
    let min_len = if len1 < len2 { len1 } else { len2 };
    
    while i < min_len
        invariant
            0 <= i <= min_len,
            min_len == if len1 < len2 { len1 } else { len2 },
            len1 == bytes1@.len(),
            len2 == bytes2@.len(),
    {
        if bytes1[i] < bytes2[i] {
            return true;
        } else if bytes1[i] > bytes2[i] {
            return false;
        }
        i += 1;
    }
    
    len1 <= len2
}
// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1@.len() == x2@.len(),
    ensures 
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == string_le(x1@[i], x2@[i]),
        forall|i: int| 0 <= i < result@.len() ==> (result@[i] == true <==> string_le(x1@[i], x2@[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result@.len() ==> result@[i] == true,
        forall|i: int| 0 <= i < result@.len() ==> (string_le(x1@[i], x2@[i]) && string_le(x2@[i], x1@[i])) ==> x1@[i] == x2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implement actual string comparison logic */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == string_le(x1@[j], x2@[j]),
    {
        let cmp = string_less_equal_impl(&x1[i], &x2[i]);
        result.push(cmp);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}