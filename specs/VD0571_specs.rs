// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
    decreases j - i
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

spec fn insert_bogus_chars(s: Seq<char>, bogus: char) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![bogus]
    } else {
        let s_old = insert_bogus_chars(s.drop_first(), bogus);
        seq![bogus].add(seq![s[0]]).add(s_old)
    }
}

fn argmax(a: Vec<i32>, start: usize) -> (result: (usize, i32))
    requires 0 <= start < a.len()
    ensures ({
        let (idx, val) = result;
        &&& start <= idx < a.len()
        &&& a@[idx as int] == val
        &&& forall|i: int| start <= i < a.len() ==> a@[i] <= val
    })
    decreases a.len() - start
{
    assume(false);
    unreached()
}

spec fn inbound_radius(s_prime: Seq<char>, c: int, r: int) -> bool {
    r >= 0 && 0 <= c-r && c+r < s_prime.len()
}

spec fn palindromic_radius(s_prime: Seq<char>, c: int, r: int) -> bool
    recommends inbound_radius(s_prime, c, r)
{
    palindromic(s_prime, c-r, c+r+1)
}

spec fn max_radius(s_prime: Seq<char>, c: int, r: int) -> bool {
    &&& inbound_radius(s_prime, c, r)
    &&& palindromic_radius(s_prime, c, r)
    &&& forall|r_prime: int| r_prime > r && inbound_radius(s_prime, c, r_prime) ==> !palindromic_radius(s_prime, c, r_prime)
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn max_interval_for_same_center(s: Seq<char>, k: int, lo: int, hi: int) -> bool {
    &&& 0 <= lo <= hi <= s.len()
    &&& lo + hi == k
    &&& palindromic(s, lo, hi)
    &&& forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == k ==> j - i <= hi - lo
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn expand_from_center(s: Seq<char>, i0: usize, j0: usize) -> (result: (usize, usize))
    requires 0 <= i0 <= j0 <= s.len(),
             palindromic(s, i0 as int, j0 as int)
    ensures 
        ({
            let (lo, hi) = result;
            &&& 0 <= lo <= hi <= s.len()
            &&& palindromic(s, lo as int, hi as int)
            &&& forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j)
              && i + j == i0 + j0
              ==> j - i <= hi - lo
        })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}