// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat {
    nums.filter(|elem: i32| elem == x).len()
}

spec fn filter_equal(nums: Seq<i32>, x: i32) -> Seq<i32> {
    nums.filter(|elem: i32| elem == x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): xor helpers using Seq::slice to operate on subsequences */
spec fn seq_xor(s: Seq<i32>) -> i32 {
    if s.len() == 0 {
        0
    } else {
        seq_xor(Seq::slice(s, 1, s.len())) ^ s.index(0)
    }
}

proof fn xor_pairs_zero(s: Seq<i32>)
    requires
        forall|x: i32| s.contains(x) ==> count_occurrences(s, x) == 2,
    ensures
        seq_xor(s) == 0,
{
    if s.len() == 0 {
        assert(seq_xor(s) == 0);
    } else {
        let x = s.index(0);
        let k: nat = choose|k: nat| k < s.len() && k > 0 && s.index(k) == x;
        let s_without = Seq::slice(s, 1, k) + Seq::slice(s, k + 1, s.len());
        xor_pairs_zero(s_without);
        assert(seq_xor(s) == seq_xor(s_without) ^ x ^ x);
        assert(seq_xor(s_without) == 0);
        assert(seq_xor(s) == 0);
    }
}

proof fn xor_seq_unique(s: Seq<i32>)
    requires
        s.len() > 0,
        exists|u: i32| count_occurrences(s, u) == 1,
        forall|elem: i32| s.contains(elem) ==> (count_occurrences(s, elem) == 1 || count_occurrences(s, elem) == 2),
    ensures
        count_occurrences(s, seq_xor(s)) == 1,
        forall|x: i32| s.contains(x) ==> (x == seq_xor(s) || count_occurrences(s, x) == 2),
{
    if s.len() == 1 {
        assert(seq_xor(s) == s.index(0));
        assert(count_occurrences(s, seq_xor(s)) == 1);
    } else {
        let x = s.index(0);
        if count_occurrences(s, x) == 1 {
            let tail = Seq::slice(s, 1, s.len());
            xor_pairs_zero(tail);
            assert(seq_xor(s) == seq_xor(tail) ^ x);
            assert(seq_xor(tail) == 0);
            assert(seq_xor(s) == x);
            assert(count_occurrences(s, seq_xor(s)) == 1);
        } else {
            let k: nat = choose|k: nat| k < s.len() && k > 0 && s.index(k) == x;
            let s2 = Seq::slice(s, 1, k) + Seq::slice(s, k + 1, s.len());
            xor_seq_unique(s2);
            assert(seq_xor(s) == seq_xor(s2) ^ x ^ x);
            assert(seq_xor(s) == seq_xor(s2));
            assert(count_occurrences(s, seq_xor(s)) == 1);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
    ensures
        count_occurrences(nums@, result) == 1,
        forall|x: i32| nums@.contains(x) ==> (x == result || count_occurrences(nums@, x) == 2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute xor accumulator and prove unique using seq_xor */
    let mut acc: i32 = 0;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            acc == seq_xor(Seq::slice(nums@, 0, i)),
            i <= nums.len(),
        decreases nums.len() - i
    {
        let v = nums[i];
        acc ^= v;
        i += 1;
    }
    proof {
        xor_seq_unique(nums@);
        assert(acc == seq_xor(nums@));
        assert(count_occurrences(nums@, acc) == 1);
    }
    acc
}

// </vc-code>

}
fn main() {}