use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end

// <vc-helpers>
// No updates needed for helpers section as the issue is in the code section related to a missing decreases clause.
// </vc-helpers>

// <vc-spec>
fn to_lowercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<char> = Vec::with_capacity(str1.len());
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == (if (str1[k] >= 'A' && str1[k] <= 'Z') {
                ((str1[k] as u8) + 32) as char
            } else {
                str1[k]
            }),
        decreases str1.len() - i
    {
        let c = str1[i];
        if c >= 'A' && c <= 'Z' {
            result.push(((c as u8) + 32) as char);
        } else {
            result.push(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}