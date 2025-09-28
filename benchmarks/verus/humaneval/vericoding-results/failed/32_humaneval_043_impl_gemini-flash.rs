// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed `lemma` keyword for `fn` */
fn lemma_has_pair_sum_to_zero_monotonic(s: Seq<int>, lo: int, hi: int, i: int, j: int)
    requires
        0 <= lo <= i < j < hi <= s.len(),
        s[i] + s[j] == 0
    ensures
        has_pair_sum_to_zero(s.subsequence(lo, hi))
{
    let sub_seq = s.subsequence(lo, hi);
    let new_i = i - lo;
    let new_j = j - lo;
    assert(0 <= new_i < new_j < sub_seq.len());
    assert(sub_seq[new_i] == s[i]);
    assert(sub_seq[new_j] == s[j]);
    assert(sub_seq[new_i] + sub_seq[new_j] == 0);
}
// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added `proof` blocks where necessary, ensuring correct sequence properties are asserted */
{
    let len = l.len();
    let s = l@.map(|i, x| x as int);

    if len < 2 {
        proof {
            assert(!has_pair_sum_to_zero(s));
        }
        return false;
    }

    let mut i = 0;
    while i < len - 1
        invariant
            0 <= i < len,
            forall|i_prime: int, j_prime: int| 0 <= i_prime < j_prime <= i ==> s[i_prime] + s[j_prime] != 0
        decreases len - i
    {
        let mut j = i + 1;
        while j < len
            invariant
                0 <= i < len,
                i < j <= len,
                forall|i_prime: int, j_prime: int| 0 <= i_prime < j_prime <= i ==> s[i_prime] + s[j_prime] != 0,
                forall|k: int| i < k < j ==> s[i] + s[k] != 0
            decreases len - j
        {
            if l[i] as int + l[j] as int == 0 {
                proof {
                    assert(s[i] + s[j] == 0);
                    lemma_has_pair_sum_to_zero_monotonic(s, 0, len, i, j);
                }
                return true;
            }
            j = j + 1;
        }
        proof {
            assert(forall|j_prime: int|
                i < j_prime < len ==> s[i] + s[j_prime] != 0
            );
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|i_prime: int, j_prime: int|
            0 <= i_prime < j_prime < len ==> s[i_prime] + s[j_prime] != 0
        );
        assert(!has_pair_sum_to_zero(s));
    }
    false
}
// </vc-code>


}

fn main() {}