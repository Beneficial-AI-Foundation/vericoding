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
exec fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}

exec fn shift32_exec(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == shift32_spec(c)
{
    ((c as u8) + 32) as char
}
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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    while i < str1.len()
        invariant
            i <= str1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (if is_upper_case(str1[j]) {
                shift32_spec(str1[j])
            } else {
                str1[j]
            }),
        decreases str1.len() - i
    {
        let c = str1[i];
        /* code modified by LLM (iteration 2): replaced spec function calls with exec versions */
        if is_upper_case_exec(c) {
            result.push(shift32_exec(c));
        } else {
            result.push(c);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}