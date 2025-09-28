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
// Helper lemma to prove that if no_letters holds for the entire sequence, then no element is a letter
proof fn no_letters_implies_all_not_letters(s: Seq<char>)
    ensures
        no_letters(s, s.len() as nat) ==> forall|i: int| 0 <= i < s.len() ==> !is_letter(s[i])
{
    if no_letters(s, s.len() as nat) {
        assert forall|i: int| 0 <= i < s.len() implies !is_letter(s[i]) by {
            assert(no_letters(s, s.len() as nat));
        }
    }
}

// Helper lemma for reverse property
proof fn reverse_property_helper(s: Seq<char>, result: Seq<char>, n: nat)
    requires
        n <= s.len(),
        result.len() == s.len(),
        forall|i: int| 0 <= i < n ==> result[s.len() - 1 - i] == s[i]
    ensures
        forall|i: int| 0 <= i < n ==> result[s.len() - 1 - i] == s[i]
{
}

// Executable version of is_letter
fn is_letter_exec(c: char) -> (result: bool)
    ensures result == is_letter(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
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
    let mut i: usize = 0;
    
    // Check if string contains any letters
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_letter <==> !no_letters(s@, i as nat),
            has_letter ==> exists|j: int| 0 <= j < i && is_letter(s@[j])
        decreases s.len() - i
    {
        if is_letter_exec(s[i]) {
            has_letter = true;
            assert(!no_letters(s@, (i + 1) as nat));
        }
        i = i + 1;
    }
    
    if has_letter {
        // Toggle case for all letters
        let mut result = Vec::new();
        let mut j: usize = 0;
        
        assert(!no_letters(s@, s@.len() as nat));
        
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                result@.len() == j,
                forall|k: int| 0 <= k < j && is_letter(s@[k]) ==> result@[k] == toggle_case(s@[k]),
                forall|k: int| 0 <= k < j && !is_letter(s@[k]) ==> result@[k] == s@[k]
            decreases s.len() - j
        {
            if is_letter_exec(s[j]) {
                let c = s[j];
                if c >= 'a' && c <= 'z' {
                    let toggled = ((c as u8 - 'a' as u8 + 'A' as u8) as char);
                    result.push(toggled);
                } else {
                    assert(c >= 'A' && c <= 'Z');
                    let toggled = ((c as u8 - 'A' as u8 + 'a' as u8) as char);
                    result.push(toggled);
                }
            } else {
                result.push(s[j]);
            }
            j = j + 1;
        }
        
        assert(result@.len() == s@.len());
        assert(forall|i: int| 0 <= i < s@.len() && is_letter(s@[i]) ==> result@[i] == toggle_case(s@[i]));
        assert(forall|i: int| 0 <= i < s@.len() && !is_letter(s@[i]) ==> result@[i] == s@[i]);
        
        result
    } else {
        // No letters, so reverse the string
        assert(no_letters(s@, s@.len() as nat));
        proof { no_letters_implies_all_not_letters(s@); }
        
        let reversed = reverse(s);
        
        // Prove is_reverse property
        assert(reversed@.len() == s@.len());
        assert forall|si: int| 0 <= si < s@.len()/2 implies reversed@[s@.len() - si - 1] == s@[si] by {
            assert(reversed@[s@.len() - 1 - si] == s@[si]);
            assert(s@.len() - si - 1 == s@.len() - 1 - si);
        }
        assert(is_reverse(reversed@, s@));
        
        reversed
    }
}
// </vc-code>

fn main() {}

}