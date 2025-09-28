// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_decimal_char(c: char) -> bool {
    ('0' <= c && c <= '9')
}

spec fn all_chars_decimal(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_decimal_char(s[0]) && all_chars_decimal(s.skip(1))
    }
}

fn isdecimal(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (result[i] == true <==> (a[i]@.len() > 0 && all_chars_decimal(a[i]@)))
            &&& (a[i]@ == Seq::<char>::empty() ==> result[i] == false)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Removed ghost types from executable code */
{
    let mut result = Vec::new();
    for s in a.iter() {
        let chars: Vec<char> = s.chars().collect();
        if chars.len() == 0 {
            result.push(false);
        } else {
            let mut all_decimal = true;
            let mut i = 0;
            while i < chars.len()
                invariant
                    0 <= i as nat <= chars.len() as nat,
                decreases (chars.len() - i) as nat
            {
                if chars[i] < '0' || chars[i] > '9' {
                    all_decimal = false;
                    break;
                }
                i += 1;
            }
            result.push(all_decimal);
        }
    }
    result
}
// </vc-code>


}
fn main() {}