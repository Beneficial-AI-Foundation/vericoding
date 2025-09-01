use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
spec fn multiset_equal(seq1: Seq<i32>, seq2: Seq<i32>) -> bool {
    forall|x: i32| (#[trigger] seq1.count(|y| y == x)) == (#[trigger] seq2.count(|y| y == x))
}

spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

proof fn lemma_multiset_equal_reflexive(seq: Seq<i32>)
    ensures
        multiset_equal(seq, seq),
{
}

proof fn lemma_sorted_permutation_preserves_sorted(seq1: Seq<i32>, seq2: Seq<i32>)
    requires
        sorted(seq1),
        multiset_equal(seq1, seq2),
        sorted(seq2),
    ensures
        seq1 =~= seq2,
{
    assert(seq1.len() == seq2.len());
    for i: int in 0..seq1.len() {
        assert(seq1[i] == seq2[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut ret = s.clone();
    let n = ret.len();
    
    proof {
        lemma_multiset_equal_reflexive(s@);
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            ret@.len() == n,
            multiset_equal(s@, ret@),
        decreases n - i,
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= j <= n - i - 1,
                ret@.len() == n,
                multiset_equal(s@, ret@),
            decreases n - i - 1 - j,
        {
            assert(j < ret.len());
            assert(j + 1 < ret.len());
            if ret[j] > ret[j + 1] {
                let temp = ret[j];
                ret.set(j, ret[j + 1]);
                ret.set(j + 1, temp);
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        assert(sorted(ret@));
        lemma_sorted_permutation_preserves_sorted(s@, ret@);
    }
    
    ret
}
// </vc-code>

fn main() {}
}