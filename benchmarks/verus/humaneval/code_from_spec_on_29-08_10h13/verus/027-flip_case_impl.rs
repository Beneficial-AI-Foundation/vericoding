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
proof fn shift_plus_32_correct(c: char)
    requires is_upper_case(c)
    ensures shift_plus_32_spec(c) == ((c as u8) + 32) as char
{
}

proof fn shift_minus_32_correct(c: char)
    requires is_lower_case(c)
    ensures shift_minus_32_spec(c) == ((c as u8) - 32) as char
{
}

proof fn char_arithmetic_bounds(c: char)
    requires is_upper_case(c) || is_lower_case(c)
    ensures 
        is_upper_case(c) ==> (c as u8) + 32 <= 255,
        is_lower_case(c) ==> (c as u8) >= 32
{
}

fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}

fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def flip_case(string: str) -> str"
docstring: |
For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
test_cases:
- input: "Hello"
expected_output: "hELLO"
*/
// </vc-description>

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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    while i < str.len()
        invariant
            i <= str.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == flip_case_spec(#[trigger] str[j])
        decreases str.len() - i
    {
        let c = str[i];
        let flipped_c = if is_lower_case_exec(c) {
            proof {
                char_arithmetic_bounds(c);
            }
            ((c as u8) - 32) as char
        } else if is_upper_case_exec(c) {
            proof {
                char_arithmetic_bounds(c);
            }
            ((c as u8) + 32) as char
        } else {
            c
        };
        
        result.push(flipped_c);
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!
fn main() {}