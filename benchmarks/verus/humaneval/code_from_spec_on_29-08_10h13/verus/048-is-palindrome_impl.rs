use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn reverse_string(s: Seq<char>) -> Seq<char> {
    s.reverse()
}

proof fn palindrome_property(s: Seq<char>)
    ensures s == reverse_string(s) <==> (forall|i: int| 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i])
{
    if s == reverse_string(s) {
        assert forall|i: int| 0 <= i < s.len() implies s[i] == s[s.len() - 1 - i] by {
            assert(s[i] == reverse_string(s)[i]);
            assert(reverse_string(s)[i] == s[s.len() - 1 - i]);
        }
    }
    
    if forall|i: int| 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i] {
        assert(s == reverse_string(s)) by {
            assert(s.len() == reverse_string(s).len());
            assert forall|i: int| 0 <= i < s.len() implies s[i] == reverse_string(s)[i] by {
                assert(s[i] == s[s.len() - 1 - i]);
                assert(reverse_string(s)[i] == s[s.len() - 1 - i]);
            }
        }
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def is_palindrome(string: str) -> Bool"
docstring: |
Checks if given string is a palindrome
test_cases:
- input: ""
expected_output: True
- input: "aba"
expected_output: True
- input: "aaaaa"
expected_output: "True"
- input: "zbcd"
expected_output: "False"
*/
// </vc-description>

// <vc-spec>
fn is_palindrome(string: &str) -> (result: bool)
    ensures result == (string@.reverse() == string@)
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatch by casting len to int for division */
    let len = string@.len();
    let ghost_len: int = len as int;
    
    for i in 0..(ghost_len/2) as nat
        invariant
            len == string@.len(),
            ghost_len == len as int,
            forall|j: int| 0 <= j < i ==> string@[j] == string@[len - 1 - j]
    {
        proof {
            let ghost_i: int = i as int;
            if string@[ghost_i] != string@[ghost_len - 1 - ghost_i] {
                assert(string@[ghost_i] != string@[ghost_len - 1 - ghost_i]);
                assert(string@.reverse()[ghost_i] == string@[ghost_len - 1 - ghost_i]);
                assert(string@ != string@.reverse());
                return false;
            }
        }
    }
    
    proof {
        assert forall|i: int| 0 <= i < string@.len() implies string@[i] == string@[string@.len() - 1 - i] by {
            if i < ghost_len / 2 {
                assert(string@[i] == string@[len - 1 - i]);
            } else if i >= ghost_len / 2 {
                let j = ghost_len - 1 - i;
                if j < ghost_len / 2 {
                    assert(string@[j] == string@[len - 1 - j]);
                    assert(string@[i] == string@[len - 1 - i]);
                }
            }
        }
        assert(string@ == string@.reverse());
    }
    
    true
}
// </vc-code>

}
fn main() {}