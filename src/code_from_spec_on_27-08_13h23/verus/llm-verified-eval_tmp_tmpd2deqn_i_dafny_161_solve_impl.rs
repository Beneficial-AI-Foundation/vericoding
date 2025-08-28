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
proof fn lemma_toggle_case_idempotent(c: char)
    ensures
        is_letter(c) ==> toggle_case(toggle_case(c)) == c
{
    if is_letter(c) {
        if c >= 'a' && c <= 'z' {
            assert(toggle_case(c) == ((c as u8 - 'a' as u8 + 'A' as u8) as char));
            assert(toggle_case(toggle_case(c)) == c);
        } else {
            assert(c >= 'A' && c <= 'Z');
            assert(toggle_case(c) == ((c as u8 - 'A' as u8 + 'a' as u8) as char));
            assert(toggle_case(toggle_case(c)) == c);
        }
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
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
{
    let mut has_letter = false;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            has_letter ==> !no_letters(s@, s@.len() as nat)
    {
        if is_letter(s[i as int]) {
            has_letter = true;
        }
        i = i + 1;
    }

    let mut result = Vec::new();
    let mut j = 0;
    if has_letter {
        while j < s.len()
            invariant
                0 <= j <= s@.len(),
                result@.len() == j as nat,
                forall|k: int| 0 <= k < j && is_letter(s@[k]) ==> result@[k] == toggle_case(s@[k]),
                forall|k: int| 0 <= k < j && !is_letter(s@[k]) ==> result@[k] == s@[k]
        {
            if is_letter(s[j as int]) {
                result.push(toggle_case(s[j as int]));
            } else {
                result.push(s[j as int]);
            }
            j = j + 1;
        }
    } else {
        let mut reversed = Vec::new();
        let s_len = s.len();
        let mut k = 0;
        while k < s_len
            invariant
                0 <= k <= s_len,
                reversed@.len() == k as nat,
                forall|i: int| 0 <= i < k ==> reversed@[i] == s@[(s_len - 1 - i) as nat]
        {
            reversed.push(s[(s_len - 1 - k) as int]);
            k = k + 1;
        }
        result = reversed;
    }
    result
}
// </vc-code>

fn main() {}

}