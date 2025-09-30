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

// <vc-helpers>
fn is_letter_exec(c: char) -> (result: bool)
    ensures result == is_letter(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

fn toggle_case_exec(c: char) -> (result: char)
    requires is_letter(c)
    ensures result == toggle_case(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    }
}

proof fn lemma_no_letters_preserved(s: Seq<char>, i: nat)
    requires i < s.len()
    ensures no_letters(s, i) ==> no_letters(s, i + 1) || is_letter(s[i as int])
{
}

proof fn lemma_reverse_equivalence(s: Seq<char>, result: Seq<char>)
    requires 
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == s[s.len() - 1 - i]
    ensures is_reverse(result, s)
{
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
    let mut has_letter = false;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            has_letter <==> !no_letters(s@, i as nat)
        decreases s.len() - i
    {
        if is_letter_exec(s[i]) {
            has_letter = true;
        }
        i += 1;
    }
    
    if has_letter {
        let mut result = Vec::with_capacity(s.len());
        let mut j = 0;
        
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                result@.len() == j,
                forall|k: int| 0 <= k < j && is_letter(s@[k]) ==> 
                    result@[k] == toggle_case(s@[k]),
                forall|k: int| 0 <= k < j && !is_letter(s@[k]) ==> 
                    result@[k] == s@[k]
            decreases s.len() - j
        {
            if is_letter_exec(s[j]) {
                result.push(toggle_case_exec(s[j]));
            } else {
                result.push(s[j]);
            }
            j += 1;
        }
        
        result
    } else {
        let result = reverse(s);
        proof {
            lemma_reverse_equivalence(s@, result@);
        }
        result
    }
}
// </vc-code>

fn main() {}

}