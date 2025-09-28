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
    if start == a.len() - 1 {
        (start, a[start])
    } else {
        let (i, v) = argmax(a.clone(), start + 1);
        if a[start] >= v { (start, a[start]) } else { (i, v) }
    }
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
/* helper modified by LLM (iteration 5): No changes made to this helper. */
proof fn lemma_palindromic_properties(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        palindromic(s, i, j),
    ensures
        forall|k: int| i <= k < j ==> s[k] == s[i + j - 1 - k],
    decreases j - i
{
    if j - i >= 2 {
        lemma_palindromic_properties(s, i + 1, j - 1);
    }
}
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
    /* code modified by LLM (iteration 5): Fixed a compilation error by splitting a chained comparison inside an assert. */
    let mut i = i0;
    let mut j = j0;

    while i > 0 && j < s.len() && s[i - 1] == s[j]
        invariant
            0 <= i <= i0,
            j0 <= j,
            i <= j,
            j as int <= s@.len(),
            palindromic(s@, i as int, j as int),
            (i as int) + (j as int) == (i0 as int) + (j0 as int),
        decreases s@.len() - (j as int - i as int),
    {
        proof {
            let i_old = i;
            let j_old = j;
            assert(s@[(i_old - 1) as int] == s@[j_old as int]);
            assert(palindromic(s@, i_old as int, j_old as int));
        }
        i = i - 1;
        j = j + 1;
    }

    let lo = i;
    let hi = j;
    
    proof {
        let center_sum = (i0 as int) + (j0 as int);
        assert((lo as int) + (hi as int) == center_sum);
        
        assert forall|i_prime: int, j_prime: int| 
            (
                0 <= i_prime <= j_prime <= s@.len() &&
                palindromic(s@, i_prime, j_prime) &&
                i_prime + j_prime == center_sum
            ) implies j_prime - i_prime <= (hi as int) - (lo as int)
        by {
            if j_prime - i_prime > (hi as int) - (lo as int) {
                assert(i_prime < lo as int);
                assert(j_prime > hi as int);

                if lo == 0 {
                    assert(i_prime < 0);
                    assert(false);
                } else if hi as int == s@.len() {
                    assert(j_prime > s@.len());
                    assert(false);
                } else {
                    assert(s@[(lo - 1) as int] != s@[hi as int]);

                    lemma_palindromic_properties(s@, i_prime, j_prime);
                    assert(i_prime <= (lo - 1) as int && (lo - 1) as int < j_prime);
                    
                    assert(s@[(lo - 1) as int] == s@[i_prime + j_prime - 1 - (lo - 1) as int]);
                    assert(s@[(lo - 1) as int] == s@[center_sum - lo as int]);
                    assert(s@[(lo - 1) as int] == s@[hi as int]);
                    assert(false);
                }
            }
        };
    }

    (lo, hi)
}
// </vc-code>

}
fn main() {}