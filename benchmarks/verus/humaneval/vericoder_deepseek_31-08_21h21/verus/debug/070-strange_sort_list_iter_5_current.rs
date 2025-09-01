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
    for i in 0..seq1.len() {
        assert(seq1[i] == seq2[i]);
    }
}

proof fn lemma_swap_preserves_multiset(seq1: Seq<i32>, seq2: Seq<i32>, i: int, j: int)
    requires
        0 <= i < seq1.len(),
        0 <= j < seq1.len(),
        seq2 == seq1.update(i, seq1[j]).update(j, seq1[i]),
    ensures
        multiset_equal(seq1, seq2),
{
}

proof fn lemma_bubble_sort_sorted(seq: Seq<i32>, n: nat) -> (ret: Seq<i32>)
    ensures
        sorted(ret),
        multiset_equal(seq, ret),
        ret.len() == seq.len(),
{
    if n == 0 {
        seq
    } else {
        let mut temp = seq;
        let mut j: int = 0;
        while j < n as int - 1
            invariant
                0 <= j <= n as int - 1,
                temp.len() == seq.len(),
                multiset_equal(seq, temp),
            decreases n as int - 1 - j,
        {
            if temp[j] > temp[j + 1] {
                let temp_j = temp[j];
                let temp_j1 = temp[j + 1];
                temp = temp.update(j, temp_j1).update(j + 1, temp_j);
                lemma_swap_preserves_multiset(temp.update(j, temp_j).update(j + 1, temp_j1), temp, j, j + 1);
            }
            j += 1;
        }
        let sorted_tail = lemma_bubble_sort_sorted(temp, n - 1);
        sorted_tail
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
                let temp_j = ret[j];
                let temp_j1 = ret[j + 1];
                ret.set(j, temp_j1);
                ret.set(j + 1, temp_j);
                proof {
                    lemma_swap_preserves_multiset(ret@.update(j, temp_j).update(j + 1, temp_j1), ret@, j as int, (j + 1) as int);
                }
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