pub fn isPalindrome(s: &[char]) -> (result: bool)
    requires(1 <= s.len() <= 200000)
    ensures(result <==> (forall|i: usize| 0 <= i < s.len() / 2 ==> s[i] == s[s.len() - 1 - i]))
{
}