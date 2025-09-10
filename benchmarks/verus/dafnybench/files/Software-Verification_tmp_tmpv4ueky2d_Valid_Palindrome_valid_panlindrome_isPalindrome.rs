use vstd::prelude::*;

verus! {

fn isPalindrome(s: &Vec<char>) -> (result: bool)
    requires 1 <= s.len() <= 200000,
    ensures result <==> (forall|i: int| 0 <= i < (s.len() as int) / 2 ==> s[i] == s[(s.len() as int) - 1 - i])
{
    assume(false);
    unreached()
}

}
fn main() {}