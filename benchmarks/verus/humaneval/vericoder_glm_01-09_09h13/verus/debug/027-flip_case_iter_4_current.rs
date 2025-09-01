use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_plus_32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn flip_case_spec(c: char) -> (result:char) {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else if is_upper_case(c) {
        shift_plus_32_spec(c)
    } else {
        c
    }
}
// pure-end

// <vc-helpers>
exec fn flip_case_exec(c: char) -> (result: char)
    ensures result == flip_case_spec(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn flip_case(str: &[char]) -> (flipped_case: Vec<char>)
    // post-conditions-start
    ensures
        str@.len() == flipped_case@.len(),
        forall|i: int| 0 <= i < str.len() ==> flipped_case[i] == flip_case_spec(#[trigger] str[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = str.len();
    let mut result = Vec::new();
    for i in 0..n
        invariant
            result@.len() == i,
            i <= n,
            invariant_except_break(i < n),
            forall|j: int| 0 <= j < i ==> 
                result@[j] == flip_case_spec(#[trigger] str[j])
    {
        let c = str[i];
        let flipped = flip_case_exec(c);
        result.push(flipped);
    }
    result
}
// </vc-code>

} // verus!
fn main() {}