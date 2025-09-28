// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate spec declaration and fixed sequence conversion */
spec fn is_alphanumeric_char(c: char) -> bool {
    let code = c as int;
    (code >= 0x30 && code <= 0x39) ||  // 0-9
    (code >= 0x41 && code <= 0x5A) ||  // A-Z
    (code >= 0x61 && code <= 0x7A)     // a-z
}

spec fn string_to_seq(s: &String) -> Seq<char> {
    Seq::<char>::new(s.len() as nat, |i: int| s.as_bytes()[i] as char)
}
// </vc-helpers>

// <vc-spec>
spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): removed duplicate spec declaration and simplified implementation */
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j].len() > 0 && all_chars_alphanumeric(a@[j])),
        decreases a.len() - i
    {
        let s = &a[i];
        let mut all_alpha = s.len() > 0;
        let mut j: usize = 0;
        
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                all_alpha == (j == 0 && s.len() > 0 || j > 0 && all_chars_alphanumeric(s@.subrange(0, j))),
                all_alpha ==> forall|k: int| 0 <= k < j ==> is_alphanumeric_char(s@[k])
            decreases s.len() - j
        {
            let c = s.as_bytes()[j] as char;
            if !is_alphanumeric_char(c) {
                all_alpha = false;
                break;
            }
            j += 1;
        }
        
        result.push(all_alpha);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}