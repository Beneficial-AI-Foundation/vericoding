use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
use vstd::assert_by_contradiction;

spec fn is_even_seq(s: Seq<int>) -> Seq<int> {
    s.filter(|x| is_even(x))
}

spec fn is_odd_seq(s: Seq<int>) -> Seq<int> {
    s.filter(|x| is_odd(x))
}

proof fn lemma_first_even_found(a_seq: Seq<int>, i: int, first_even_idx: int)
    requires
        0 <= i <= a_seq.len(),
        exists |k: int| 0 <= k < a_seq.len() && is_even(a_seq[k]),
        first_even_idx == -1 || (0 <= first_even_idx < i as int && is_even(a_seq[first_even_idx])),
        forall|k: int| 0 <= k < i && is_even(a_seq[k]) ==> (first_even_idx != -1 && first_even_idx <= k),
    ensures
        first_even_idx != -1,
{
    let idx_of_first_even = a_seq.index_of_first(|x| is_even(x));
    assert(idx_of_first_even.is_Some());
    let fe_idx = idx_of_first_even.get_Some_0();
    assert(0 <= fe_idx < a_seq.len());
    assert(is_even(a_seq[fe_idx]));

    if (first_even_idx == -1) {
        if fe_idx < i {
             // If fe_idx >= i, and i reaches a_seq.len(), then fe_idx must be outside [0, i-1] after loop.
            // But fe_idx is guaranteed to be in a_seq.len()'s range.
            // For first_even_idx to remain -1, it means no even number was found up to i.
            // This implies for all k < i, is_odd(a_seq[k]).
            // If fe_idx >= i, and i reached a_seq.len(), then fe_idx must be >= a_seq.len(), which contradicts fe_idx < a_seq.len().
            // Thus fe_idx must be less than `i` (which is `a.len()` at loop termination).
            // assert(i == a_seq.len()); // This is loop termination state.
            // assert(fe_idx < a_seq.len()); // from index_of_first
            // assert(fe_idx < i);
            assert_by_contradiction!(
                {
                    assert(first_even_idx == -1);
                    assert(fe_idx < i);
                    assert(is_even(a_seq[fe_idx]));
                    assert(forall|k: int| 0 <= k < i && is_even(a_seq[k]) ==> (first_even_idx != -1 && first_even_idx <= k));
                    // Instantiate the forall with k = fe_idx
                    assert(0 <= fe_idx < i);
                    assert(is_even(a_seq[fe_idx]));
                    assert(first_even_idx != -1 && first_even_idx <= fe_idx);
                },
                first_even_idx == -1,
            );
        }
    }
}

proof fn lemma_first_odd_found(a_seq: Seq<int>, j: int, first_odd_idx: int)
    requires
        0 <= j <= a_seq.len(),
        exists |k: int| 0 <= k < a_seq.len() && is_odd(a_seq[k]),
        first_odd_idx == -1 || (0 <= first_odd_idx < j as int && is_odd(a_seq[first_odd_idx])),
        forall|k: int| 0 <= k < j && is_odd(a_seq[k]) ==> (first_odd_idx != -1 && first_odd_idx <= k),
    ensures
        first_odd_idx != -1,
{
    let idx_of_first_odd = a_seq.index_of_first(|x| is_odd(x));
    assert(idx_of_first_odd.is_Some());
    let fo_idx = idx_of_first_odd.get_Some_0();
    assert(0 <= fo_idx < a_seq.len());
    assert(is_odd(a_seq[fo_idx]));

    if (first_odd_idx == -1) {
        if fo_idx < j {
            assert_by_contradiction!(
                {
                    assert(first_odd_idx == -1);
                    assert(fo_idx < j);
                    assert(is_odd(a_seq[fo_idx]));
                    assert(forall|k: int| 0 <= k < j && is_odd(a_seq[k]) ==> (first_odd_idx != -1 && first_odd_idx <= k));
                    assert(0 <= fo_idx < j);
                    assert(is_odd(a_seq[fo_idx]));
                    assert(first_odd_idx != -1 && first_odd_idx <= fo_idx);
                },
                first_odd_idx == -1,
            );
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &[i32]) -> (diff: i32)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 
            0 <= j < a.len() && 
            is_even(a[i] as int) && 
            is_odd(a[j] as int) && 
            diff == a[i] - a[j] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k] as int)) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k] as int))
// </vc-spec>
// <vc-code>
{
    let a_seq = a.to_seq();
    
    let mut first_even_val: i32 = 0;
    let mut first_even_idx: int = -1;

    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            first_even_idx == -1 || (0 <= first_even_idx < i as int && is_even(a_seq[first_even_idx])),
            forall|k: int| 0 <= k < i && is_even(a_seq[k]) ==> (first_even_idx != -1 && first_even_idx <= k),
            first_even_idx == -1 || first_even_val == a_seq[first_even_idx],
            forall|k: int| 0 <= k < i && k < first_even_idx ==> is_odd(a_seq[k]),
        decreases a.len() - i
    {
        if is_even(a[i] as int) {
            if first_even_idx == -1 {
                first_even_val = a[i];
                first_even_idx = i as int;
            }
        }
        i = i + 1;
    }

    assert(first_even_idx != -1) by {
        lemma_first_even_found(a_seq, i, first_even_idx);
    }

    let mut first_odd_val: i32 = 0;
    let mut first_odd_idx: int = -1;

    let mut j: int = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            first_odd_idx == -1 || (0 <= first_odd_idx < j as int && is_odd(a_seq[first_odd_idx])),
            forall|k: int| 0 <= k < j && is_odd(a_seq[k]) ==> (first_odd_idx != -1 && first_odd_idx <= k),
            first_odd_idx == -1 || first_odd_val == a_seq[first_odd_idx],
            forall|k: int| 0 <= k < j && k < first_odd_idx ==> is_even(a_seq[k]),
        decreases a.len() - j
    {
        if is_odd(a[j] as int) {
            if first_odd_idx == -1 {
                first_odd_val = a[j];
                first_odd_idx = j as int;
            }
        }
        j = j + 1;
    }

    assert(first_odd_idx != -1) by {
        lemma_first_odd_found(a_seq, j, first_odd_idx);
    }

    assert(0 <= first_even_idx < a.len());
    assert(0 <= first_odd_idx < a.len());

    assert(is_even(a[first_even_idx] as int));
    assert(is_odd(a[first_odd_idx] as int));

    assert(forall|k: int| 0 <= k < first_even_idx ==> is_odd(a_seq[k])) by {
        let idx_of_first_even = a_seq.index_of_first(|x| is_even(x));
        assert(idx_of_first_even.is_Some());
        let expected_first_even_idx = idx_of_first_even.get_Some_0();
        assert(first_even_idx == expected_first_even_idx);
        assert(forall|k: int| #[trigger](0 <= k < expected_first_even_idx) ==> is_odd(a_seq[k]));
    };

    assert(forall|k: int| 0 <= k < first_odd_idx ==> is_even(a_seq[k])) by {
        let idx_of_first_odd = a_seq.index_of_first(|x| is_odd(x));
        assert(idx_of_first_odd.is_Some());
        let expected_first_odd_idx = idx_of_first_odd.get_Some_0();
        assert(first_odd_idx == expected_first_odd_idx);
        assert(forall|k: int| #[trigger](0 <= k < expected_first_odd_idx) ==> is_even(a_seq[k]));
    };
    
    first_even_val - first_odd_val
}
// </vc-code>

fn main() {
}

}