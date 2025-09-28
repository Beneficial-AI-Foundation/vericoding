// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn int_to_string(n: int) -> Seq<char> {
    unimplemented!()
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    exists|k: int| k >= 1 && k <= 10000 && stdin_input == int_to_string(k).push('\n')
}

spec fn kth_perfect_number(k: int) -> int
    recommends k >= 1 && k <= 10000
{
    if k == 1 { 19 }
    else if k == 2 { 28 }
    else if k == 3 { 37 }
    else if k == 4 { 46 }
    else if k == 5 { 55 }
    else if k == 6 { 64 }
    else if k == 7 { 73 }
    else if k == 8 { 82 }
    else if k == 9 { 91 }
    else if k == 10 { 109 }
    else { 10 * (k - 9) + 99 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires valid_input(stdin_input@)
    ensures (exists|k: int| k >= 1 && k <= 10000 && 
        stdin_input@ == int_to_string(k).push('\n') &&
        result@ == int_to_string(kth_perfect_number(k)).push('\n')) &&
        result@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed push_char to push for String operations */
    let input_chars = stdin_input@;
    let mut k: u32 = 0;
    let mut i: usize = 0;
    let input_len = stdin_input.unicode_len();
    
    while i < input_len
        invariant
            0 <= i <= input_len,
            input_len == stdin_input@.len(),
            valid_input(stdin_input@),
            forall|j: int| 0 <= j < i ==> stdin_input@[j] != '\n',
            k <= 10000,
    {
        let c = stdin_input.get_char(i);
        if c == '\n' {
            break;
        }
        assert(c >= '0' && c <= '9');
        k = k * 10 + (c as u32 - '0' as u32);
        i = i + 1;
    }
    
    assert(k >= 1 && k <= 10000);
    let ghost k_int: int = k as int;
    assert(stdin_input@ == int_to_string(k_int).push('\n'));
    
    let ghost perfect_int: int = kth_perfect_number(k_int);
    let perfect: u32 = if k == 1 { 19 }
        else if k == 2 { 28 }
        else if k == 3 { 37 }
        else if k == 4 { 46 }
        else if k == 5 { 55 }
        else if k == 6 { 64 }
        else if k == 7 { 73 }
        else if k == 8 { 82 }
        else if k == 9 { 91 }
        else if k == 10 { 109 }
        else { 10 * (k - 9) + 99 };
    
    assert(perfect == perfect_int as u32);
    
    let mut result_str = String::new();
    let mut temp = perfect;
    let mut digits: Vec<char> = Vec::new();
    
    if temp == 0 {
        digits.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
                perfect == perfect_int as u32,
                k >= 1 && k <= 10000,
        {
            let digit = ((temp % 10) + '0' as u32) as u8 as char;
            digits.push(digit);
            temp = temp / 10;
        }
    }
    
    let mut j: usize = digits.len();
    while j > 0
        invariant
            j <= digits.len(),
            perfect == perfect_int as u32,
            k >= 1 && k <= 10000,
    {
        j = j - 1;
        result_str.push(digits[j]);
    }
    
    result_str.push('\n');
    
    assert(result_str@ == int_to_string(perfect_int).push('\n'));
    assert(result_str@.len() > 0);
    
    result_str
}
// </vc-code>


}

fn main() {}