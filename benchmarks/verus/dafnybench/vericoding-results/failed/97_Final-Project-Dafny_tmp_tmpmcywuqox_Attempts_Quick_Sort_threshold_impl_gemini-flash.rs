use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
fn contains_greater_than(s: Seq<int>, x: int) -> bool
    ensures
        contains_greater_than(s, x) == exists |elem: int| #[trigger] s.contains(elem) && elem > x
{
    s.contains(|e| e > x)
}

fn contains_less_than(s: Seq<int>, x: int) -> bool
    ensures
        contains_less_than(s, x) == exists |elem: int| #[trigger] s.contains(elem) && elem < x
{
    s.contains(|e| e < x)
}
// </vc-helpers>

// <vc-spec>
fn threshold(thres: int, seq: Seq<int>) -> (ret: (Seq<int>, Seq<int>))
    ensures 
        (forall|x: int| ret.0.contains(x) ==> x <= thres) &&
        (forall|x: int| ret.1.contains(x) ==> x >= thres) &&
        ret.0.len() + ret.1.len() == seq.len() &&
        ret.0.to_multiset().add(ret.1.to_multiset()) == seq.to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut less_equal_than_thres: Vec<int> = Vec::new();
    let mut greater_equal_than_thres: Vec<int> = Vec::new();

    let mut i: int = 0;

    #[invariant]
    // i is within bounds
    i <= seq.len() &&
    // The combined length of the two vectors equals i
    less_equal_than_thres.len() + greater_equal_than_thres.len() == i &&
    // The multiset union of the two vectors equals the multiset of seq up to i
    less_equal_than_thres.to_seq().to_multiset().add(greater_equal_than_thres.to_seq().to_multiset()) == seq.subsequence(0, i).to_multiset() &&
    // All elements in less_equal_than_thres are less than or equal to thres
    (forall |x: int| #![trigger less_equal_than_thres.to_seq().contains(x)] less_equal_than_thres.to_seq().contains(x) ==> x <= thres) &&
    // All elements in greater_equal_than_thres are greater than or equal to thres (or just greater, as elements equal to thres could go to either)
    (forall |x: int| #![trigger greater_equal_than_thres.to_seq().contains(x)] greater_equal_than_thres.to_seq().contains(x) ==> x >= thres),
    decreases seq.len() - i
    loop
    {
        if i == seq.len() {
            break;
        }

        let current_val = seq.index(i);

        if current_val <= thres {
            less_equal_than_thres.push(current_val);
            proof {
                assert(less_equal_than_thres.to_seq().to_multiset() == old(less_equal_than_thres).to_seq().to_multiset().add(Multiset::singleton(current_val)));
                assert(greater_equal_than_thres.to_seq().to_multiset() == old(greater_equal_than_thres).to_seq().to_multiset());
                assert(less_equal_than_thres.to_seq().to_multiset().add(greater_equal_than_thres.to_seq().to_multiset()) == old(less_equal_than_thres).to_seq().to_multiset().add(old(greater_equal_than_thres).to_seq().to_multiset()).add(Multiset::singleton(current_val)));
                assert(old(less_equal_than_thres).to_seq().to_multiset().add(old(greater_equal_than_thres).to_seq().to_multiset()) == seq.subsequence(0, i).to_multiset());
                assert(seq.subsequence(0, i).to_multiset().add(Multiset::singleton(current_val)) == seq.subsequence(0, (i as nat) + 1).to_multiset());
            }
        } else {
            greater_equal_than_thres.push(current_val);
             proof {
                assert(greater_equal_than_thres.to_seq().to_multiset() == old(greater_equal_than_thres).to_seq().to_multiset().add(Multiset::singleton(current_val)));
                assert(less_equal_than_thres.to_seq().to_multiset() == old(less_equal_than_thres).to_seq().to_multiset());
                assert(less_equal_than_thres.to_seq().to_multiset().add(greater_equal_than_thres.to_seq().to_multiset()) == old(greater_equal_than_thres).to_seq().to_multiset().add(old(less_equal_than_thres).to_seq().to_multiset()).add(Multiset::singleton(current_val)));
                assert(old(less_equal_than_thres).to_seq().to_multiset().add(old(greater_equal_than_thres).to_seq().to_multiset()) == seq.subsequence(0, i).to_multiset());
                assert(seq.subsequence(0, i).to_multiset().add(Multiset::singleton(current_val)) == seq.subsequence(0, (i as nat) + 1).to_multiset());
            }
        }
        i = i + 1;
    }

    let ret_0 = less_equal_than_thres.to_seq();
    let ret_1 = greater_equal_than_thres.to_seq();

    // Prove postconditions
    assert forall |x: int| ret_0.contains(x) implies x <= thres by {
        assert( (forall |y: int| #![trigger less_equal_than_thres.to_seq().contains(y)] less_equal_than_thres.to_seq().contains(y) ==> y <= thres) );
    }
    assert forall |x: int| ret_1.contains(x) implies x >= thres by {
        assert( (forall |y: int| #![trigger greater_equal_than_thres.to_seq().contains(y)] greater_equal_than_thres.to_seq().contains(y) ==> y >= thres) );
    }
    assert(ret_0.len() + ret_1.len() == seq.len());
    assert(ret_0.to_multiset().add(ret_1.to_multiset()) == seq.to_multiset());

    (ret_0, ret_1)
}
// </vc-code>

fn main() {
}

}