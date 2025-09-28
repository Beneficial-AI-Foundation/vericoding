// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_letter(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

spec fn no_letters(s: Seq<char>, n: nat) -> bool
    recommends n <= s.len()
{
    forall|i: int| 0 <= i < n ==> !is_letter(s[i])
}

spec fn toggle_case(c: char) -> char {
    if c >= 'a' && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn is_reverse(s: Seq<char>, s_prime: Seq<char>) -> bool {
    (s.len() == s_prime.len()) &&
    (forall|si: int| 0 <= si < s.len()/2 ==> s_prime[s.len() - si - 1] == s[si])
}

fn reverse(original: Vec<char>) -> (reversed: Vec<char>)
    ensures 
        reversed@.len() == original@.len(),
        forall|i: int| 0 <= i < original@.len() ==> reversed@[i] == original@[original@.len() - 1 - i]
{
    assume(false);
    vec![]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): retained from previous iteration */
fn is_letter_exec(c: char) -> (b: bool)
    ensures b == is_letter(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

/* helper modified by LLM (iteration 3): retained from previous iteration */
fn toggle_case_exec(c: char) -> (res: char)
    ensures res == toggle_case(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

/* helper modified by LLM (iteration 3): retained from previous iteration */
fn contains_letter(s: &Vec<char>) -> (result: bool)
    ensures
        result == !no_letters(s@, s@.len() as nat),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            no_letters(s@, i as nat),
        decreases s.len() - i
    {
        if is_letter_exec(s[i]) {
            return true;
        }
        i = i + 1;
    }
    assert(no_letters(s@, s@.len() as nat));
    return false;
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures 
        result@.len() == s@.len(),
        !no_letters(s@, s@.len() as nat) ==> 
            forall|i: int| 0 <= i < s@.len() && is_letter(s@[i]) ==> 
                result@[i] == toggle_case(s@[i]),
        !no_letters(s@, s@.len() as nat) ==> 
            forall|i: int| 0 <= i < s@.len() && !is_letter(s@[i]) ==> 
                result@[i] == s@[i],
        no_letters(s@, s@.len() as nat) ==> is_reverse(result@, s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): replaced variable n with s.len() in reverse loop to aid verification */
    let has_letter = contains_letter(&s);

    if has_letter {
        assert(!no_letters(s@, s@.len() as nat));
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i as int ==> 
                    if is_letter(s@[j]) {
                        result@[j] == toggle_case(s@[j])
                    } else {
                        result@[j] == s@[j]
                    },
            decreases s.len() - i
        {
            let c = s[i];
            if is_letter_exec(c) {
                let toggled_c = toggle_case_exec(c);
                result.push(toggled_c);
            } else {
                result.push(c);
            }
            i = i + 1;
        }
        return result;
    } else {
        assert(no_letters(s@, s@.len() as nat));
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result.len() == i,
                forall|j: int| 0 <= j < (i as int) ==> result@[j] == s@[(s.len() as int) - 1 - j],
            decreases s.len() - i
        {
            result.push(s[s.len() - 1 - i]);
            i = i + 1;
        }
        
        proof {
            let len = s@.len();
            assert(result@.len() == len);
            assert forall|si: int| 0 <= si < len / 2 implies s@[len - 1 - si] == result@[si] by {
                assert(result@[si] == s@[len - 1 - si]);
            };
            assert(is_reverse(result@, s@));
        }
        return result;
    }
}
// </vc-code>

}
fn main() {}