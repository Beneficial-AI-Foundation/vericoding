// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn shift32(c: char) -> char {
    ((c as int) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): use ghost variables and proof blocks for conversion */
exec fn is_uppercase_exec(c: char) -> (result: bool)
    ensures result == is_uppercase(c)
{
    'A' <= c && c <= 'Z'
}

exec fn shift32_exec(c: char) -> (result: char)
    requires is_uppercase(c)
    ensures result == shift32(c)
{
    proof {
        let ghost_val = (c as int) + 32;
        assert(ghost_val == (c as int) + 32);
    }
    ((c as u8) + 32) as char
}
// </vc-helpers>

// <vc-spec>
fn to_lowercase(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if is_uppercase(s[i]) {
                result[i] == shift32(s[i])
            } else {
                result[i] == s[i]
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): add decreases clause to while loop */
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> {
                if is_uppercase(s[i]) {
                    result[i] == shift32(s[i])
                } else {
                    result[i] == s[i]
                }
            },
        decreases s.len() - idx
    {
        let c = s[idx];
        if is_uppercase_exec(c) {
            result.push(shift32_exec(c));
        } else {
            result.push(c);
        }
        idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}