// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
    decreases j - i
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

fn expand_from_center(s: Seq<char>, i0: usize, j0: usize) -> (res: (usize, usize))
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0 as int, j0 as int),
    ensures 
        res.0 <= res.1 <= s.len(),
        palindromic(s, res.0 as int, res.1 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j)  
            && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    assume(false);
    (0, 0)
}

spec fn insert_bogus_chars(s: Seq<char>, bogus: char) -> (s_prime: Seq<char>)
    decreases s.len()
{
    if s.len() == 0 {
        seq![bogus]
    } else {
        let s_prime_old = insert_bogus_chars(s.subrange(1, s.len() as int), bogus);
        let s_prime_new = seq![bogus].add(seq![s[0]]).add(s_prime_old);
        s_prime_new
    }
}

fn argmax(a: &Vec<i32>, start: usize) -> (res: (usize, i32))
    requires 0 <= start < a.len()
    ensures 
        start <= res.0 < a.len() && a[res.0 as int] == res.1,
        forall|i: int| start <= i < a.len() ==> a[i] <= res.1,
    decreases a.len() - start
{
    assume(false);
    unreached()
}

spec fn inbound_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    r >= 0 && 0 <= c-r && c+r < s_prime.len()
}

spec fn palindromic_radius(s_prime: Seq<char>, c: int, r: int) -> bool
    recommends inbound_radius(s_prime, c, r)
{
    palindromic(s_prime, c-r, c+r+1)
}

spec fn max_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    inbound_radius(s_prime, c, r)
    && palindromic_radius(s_prime, c, r)
    && (forall|r_prime: int| r_prime > r && inbound_radius(s_prime, c, r_prime) ==> !palindromic_radius(s_prime, c, r_prime))
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn max_interval_for_same_center(s: Seq<char>, k: int, lo: int, hi: int) -> bool {
    0 <= lo <= hi <= s.len()
    && lo + hi == k
    && palindromic(s, lo, hi)
    && (forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == k ==> j - i <= hi - lo)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longestPalindrome(s: Vec<char>) -> (ans: (Vec<char>, usize, usize))
    ensures 
        0 <= ans.1 <= ans.2 <= s.len(),
        ans.0@ == s@.subrange(ans.1 as int, ans.2 as int),
        palindromic(s@, ans.1 as int, ans.2 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s@, i, j) ==> j - i <= ans.2 - ans.1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}