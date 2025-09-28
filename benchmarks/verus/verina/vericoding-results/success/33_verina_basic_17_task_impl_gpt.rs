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
/* helper modified by LLM (iteration 4): spec for lowercase mapping */
spec fn lower_char_spec(c: char) -> char {
    if is_uppercase(c) { shift32(c) } else { c }
}

/* helper modified by LLM (iteration 4): executable helper avoiding invalid u32->char cast and proving relation to spec */
fn lower_char_exec(c: char) -> (result: char)
    ensures
        if is_uppercase(c) { result == shift32(c) } else { result == c }
{
    if 'A' <= c && c <= 'Z' {
        let r_u8: u8 = (c as u8) + 32u8;
        let r: char = r_u8 as char;
        proof {
            assert('A' <= c && c <= 'Z');
            assert(('Z' as int) < 256);
            assert(0 <= (c as int) && (c as int) <= ('Z' as int));
            assert(((c as u8) as int) == (c as int));
            assert(((((c as u8) as int) + 32) as char) == shift32(c));
            assert(r == ((((c as u8) as int) + 32) as char));
            assert(r == shift32(c));
        }
        r
    } else {
        c
    }
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
    /* code modified by LLM (iteration 4): build result vector with loop using helper to transform each char */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int && i as int <= s.len(),
            res.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> {
                if is_uppercase(s[j]) { res[j] == shift32(s[j]) } else { res[j] == s[j] }
            },
        decreases s.len() - i as int
    {
        let c: char = s[i];
        let lc: char = lower_char_exec(c);
        res.push(lc);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}