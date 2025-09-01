use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
spec fn multiset_equal(seq1: Seq<i32>, seq2: Seq<i32>) -> bool {
    forall|x: i32| (#[trigger] multiset_count(seq1, |y| y == x)) == (#[trigger] multiset_count(seq2, |y| y == x))
}

spec fn multiset_count(seq: Seq<i32>, f: spec_fn(i32) -> bool) -> nat
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        let count_rest = multiset_count(seq.subrange(1, seq.len() as int), f);
        if f(seq[0]) {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

proof fn lemma_multiset_equal_commutative(seq1: Seq<i32>, seq2: Seq<i32>)
    ensures
        multiset_equal(seq1, seq2) == multiset_equal(seq2, seq1),
{
}

proof fn lemma_multiset_equal_reflexive(seq: Seq<i32>)
    ensures
        multiset_equal(seq, seq),
{
    assert forall|x: i32| multiset_count(seq, |y| y == x) == multiset_count(seq, |y| y == x) by { auto };
}

proof fn lemma_multiset_count_append(seq1: Seq<i32>, seq2: Seq<i32>, f: spec_fn(i32) -> bool)
    ensures
        multiset_count(seq1.add(seq2), f) == multiset_count(seq1, f) + multiset_count(seq2, f),
    decreases seq1.len(),
{
    if seq1.len() == 0 {
        assert(seq1.add(seq2) =~= seq2);
    } else {
        lemma_multiset_count_append(seq1.subrange(1, seq1.len() as int), seq2, f);
        let first = seq1[0];
        let rest = seq1.subrange(1, seq1.len() as int);
        if f(first) {
            assert(multiset_count(seq1.add(seq2), f) == multiset_count(rest.add(seq2), f) + 1);
        } else {
            assert(multiset_count(seq1.add(seq2), f) == multiset_count(rest.add(seq2), f));
        }
    }
}

spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
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
    for i in 0..seq1.len() as int {
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
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            ret@.len() == n,
            multiset_equal(s@, ret@),
        decreases n - i,
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                0 <= j <= n - i - 1,
                ret@.len() == n,
                multiset_equal(s@, ret@),
            decreases n - i - 1 - j,
        {
            assert(j < ret.len());
            assert(j + 1 < ret.len());
            if ret.index(j) > ret.index(j + 1) {
                let temp = ret.index(j);
                ret.set(j, ret.index(j + 1));
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