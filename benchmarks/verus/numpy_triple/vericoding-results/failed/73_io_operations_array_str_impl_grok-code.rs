// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors in i8_to_string function by correcting indentation, variable declarations, and control flow */
fn i8_to_string(x: i8) -> (s: String)
{
    if x == 0 {
        "0".to_string()
    } else {
        let mut num: u32 = if (x as i32) < 0 { ((- (x as i32)) as u32) } else { (x as u32) };
        let mut s = String::new();
        if x < 0 {
            s.push('-');
        }
        let mut digit_vec = Vec<char>::new();
        while num > 0 {
            let digit = ('0' as u8) + ((num % 10) as u8);
            digit_vec.push(digit as char);
            num /= 10;
        }
        for i in 0..digit_vec.len() {
            let idx = digit_vec.len() - 1 - i;
            s.push(digit_vec[idx]);
        }
        s
    }
}
// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<i8>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented array string conversion logic with loop invariants */
    if a.len() == 0 {
        "[]".to_string()
    } else {
        let mut result = "[".to_string();
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                result@.len() > 0,
                result@[0] == '['
        {
            if i > 0 {
                result.push_str(",");
            }
            let elem_str = i8_to_string(a[i]);
            result.push_str(&elem_str);
            i += 1;
        }
        result.push_str("]");
        result
    }
}
// </vc-code>

}
fn main() {}