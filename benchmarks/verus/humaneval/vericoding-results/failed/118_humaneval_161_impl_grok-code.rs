// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_letter(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && (('A' <= s[i] && s[i] <= 'Z') || ('a' <= s[i] && s[i] <= 'z'))
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s 
    } else { 
        s.subrange(s.len() as int - 1, s.len() as int).add(reverse_string(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn swap_case(c: char) -> char
{
    if 'A' <= c && c <= 'Z' { 
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' { 
        ((c as u32 - 32) as char)
    } else { 
        c 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by using char::from_u32().unwrap() for safe char casting */
exec fn swap_case_exec(c: char) -> (ret: char)
    ensures ret == swap_case(c)
{
    if c >= 'a' && c <= 'z' {
        char::from_u32(c as u32 - 'a' as u32 + 'A' as u32).unwrap()
    } else if c >= 'A' && c <= 'Z' {
        char::from_u32(c as u32 - 'A' as u32 + 'a' as u32).unwrap()
    } else {
        c
    }
}

exec fn has_letters(v: &Vec<char>) -> (ret: bool)
    ensures ret == has_letter(v@)
{
    let mut ret = false;
    let mut index = 0;
    while index < v.len()
        invariant
            ret == (exists |i: int| #![trigger (('A' <= v@[i] && v@[i] <= 'Z') || ('a' <= v@[i] && v@[i] <= 'z'))] 0 <= i < index && (('A' <= v@[i] && v@[i] <= 'Z') || ('a' <= v@[i] && v@[i] <= 'z')))
        decreases v.len() - index
    {
        if ('A' <= v[index] && v[index] <= 'Z') || ('a' <= v[index] && v[index] <= 'z') {
            ret = true;
        }
        index += 1;
    }
    ret
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures (if has_letter(s@) {
        result@.len() == s@.len() && 
        (forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]))
    } else {
        result@ == reverse_string(s@)
    }) && result@.len() == s@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes, compilation fixed via helpers */
    if has_letters(&s) {
        let mut result: Vec<char> = Vec::new();
        let n = s.len();
        for index in 0..n
            invariant
                result.len() == index,
                forall |i: int| 0 <= i < index ==> result@[i] == swap_case(s@[i])
        {
            result.push(swap_case_exec(s[index]));
        }
        result
    } else {
        let mut result: Vec<char> = Vec::new();
        let n = s.len();
        for index in 0..n
            invariant
                result.len() == index,
                forall |i: int| 0 <= i < index ==> result@[i] == s@[n - 1 - i]
        {
            result.push(s[n - 1 - index]);
        }
        proof {
            assert(result@ == reverse_string(s@));
        }
        result
    }
}
// </vc-code>


}

fn main() {}