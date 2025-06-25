/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/

// Specifying the problem: whether `s[i..j]` is palindromic
spec fn palindromic(s: &str, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
{
    j - i < 2 || (s[i as usize] == s[(j-1) as usize] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:
proof fn lemma_palindromic_contains(s: &str, lo: int, hi: int, lo_: int, hi_: int)
    requires 0 <= lo <= lo_ <= hi_ <= hi <= s.len(),
             lo + hi == lo_ + hi_,
             palindromic(s, lo, hi)
    ensures palindromic(s, lo_, hi_)
{
}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
pub fn expand_from_center(s: &str, i0: int, j0: int) -> (lo: int, hi: int)
    requires(0 <= i0 <= j0 <= s.len()),
    requires(palindromic(s, i0, j0)),
    ensures(|result| {
        let (lo, hi) = result;
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi)
    }),
    ensures(|result| {
        let (lo, hi) = result;
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == i0 + j0 ==> j - i <= hi - lo
    })
{
}

// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
pub fn longestPalindrome(s: &str) -> (ans: String, lo: int, hi: int)
    ensures(|result| {
        let (ans, lo, hi) = result;
        0 <= lo <= hi <= s.len() && ans == s.substring(lo as usize, hi as usize)
    }),
    ensures(|result| {
        let (ans, lo, hi) = result;
        palindromic(s, lo, hi)
    }),
    ensures(|result| {
        let (ans, lo, hi) = result;
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) ==> j - i <= hi - lo
    })
{
}

pub fn longestPalindrome_(s: &str) -> (ans: String, lo: int, hi: int)
    ensures(|result| {
        let (ans, lo, hi) = result;
        0 <= lo <= hi <= s.len() && ans == s.substring(lo as usize, hi as usize)
    }),
    ensures(|result| {
        let (ans, lo, hi) = result;
        palindromic(s, lo, hi)
    }),
    ensures(|result| {
        let (ans, lo, hi) = result;
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) ==> j - i <= hi - lo
    })
{
}

pub fn insert_bogus_chars(s: &str, bogus: char) -> (s_: String)
    ensures(|s_| s_.len() == 2 * s.len() + 1),
    ensures(|s_| forall|i: int| 0 <= i <= s.len() ==> s_[(i * 2) as usize] == bogus),
    ensures(|s_| forall|i: int| 0 <= i < s.len() ==> s_[(i * 2 + 1) as usize] == s[i as usize])
{
}

pub fn argmax(a: &[int], start: int) -> (res: (int, int))
    requires(0 <= start < a.len()),
    ensures(|res| start <= res.0 < a.len() && a[res.0 as usize] == res.1),
    ensures(|res| forall|i: int| start <= i < a.len() ==> a[i as usize] <= res.1)
{
}