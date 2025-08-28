use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn isPalindrome(s: &Vec<char>) -> (result: bool)
    requires 1 <= s.len() <= 200000,
    ensures result <==> (forall|i: int| 0 <= i < (s.len() as int) / 2 ==> s[i] == s[(s.len() as int) - 1 - i])
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_palindrome(s: &Vec<char>) -> (result: bool)
    requires 1 <= s.len() <= 200000,
    ensures result <==> (forall|i: int| 0 <= i < (s.len() as int) / 2 ==> s@[i] == s@[(s.len() as int) - 1 - i])
{
    let len = s.len() as int;
    let half_len = len / 2;
    let mut i: int = 0;
    let mut is_pal = true;

    while i < half_len
        invariant 
            0 <= i <= half_len,
            is_pal <==> (forall|j: int| 0 <= j < i ==> s@[j] == s@[len - 1 - j]),
    {
        if s@[i] != s@[len - 1 - i] {
            is_pal = false;
            break;
        }
        i = i + 1;
    }
    is_pal
}
// </vc-code>

fn main() {
}

}