use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

// all the values in the range satisfy `comparer` (comparer(q[i], key) == true)
spec fn range_satisfies_comparer(q: Seq<int>, key: int, lower_bound: int, upper_bound: int, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    forall |i: int| lower_bound <= i < upper_bound ==> comparer(q[i], key)
}

// all the values in the range satisfy `!comparer` (comparer(q[i], key) == false)
spec fn range_satisfies_comparer_negation(q: Seq<int>, key: int, lower_bound: int, upper_bound: int, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    range_satisfies_comparer(q, key, lower_bound, upper_bound, |n1: int, n2: int| !comparer(n1, n2))
}

fn binary_search(q: Seq<int>, key: int, lower_bound: usize, upper_bound: usize, comparer: spec_fn(int, int) -> bool) -> (index: usize)
    requires
        sorted(q),
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, 0int, lower_bound as int, comparer),
        range_satisfies_comparer(q, key, upper_bound as int, q.len() as int, comparer),
        // comparer is '>' or '>='
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 > n2)) ||
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 >= n2))
    ensures
        lower_bound <= index <= upper_bound,
        range_satisfies_comparer_negation(q, key, 0int, index as int, comparer),
        range_satisfies_comparer(q, key, index as int, q.len() as int, comparer)
{
    assume(false);
    0
}

// <vc-helpers>
spec fn less_than(a: int, b: int) -> bool { a < b }
spec fn greater_than_or_equal(a: int, b: int) -> bool { a >= b }
spec fn greater_than(a: int, b: int) -> bool { a > b }

proof fn lemma_range_satisfies_comparer_negation_implies_less_than(q: Seq<int>, key: int, lower_bound: int, upper_bound: int)
    requires
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, lower_bound, upper_bound, FnSpec(|n1: int, n2: int| less_than(n1, n2)))
    ensures
        forall |i: int| lower_bound <= i < upper_bound ==> q[i] < key
{
}

proof fn lemma_range_satisfies_comparer_implies_greater_than_or_equal(q: Seq<int>, key: int, lower_bound: int, upper_bound: int)
    requires
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer(q, key, lower_bound, upper_bound, FnSpec(|n1: int, n2: int| greater_than_or_equal(n1, n2)))
    ensures
        forall |i: int| lower_bound <= i < upper_bound ==> q[i] >= key
{
}

proof fn lemma_range_satisfies_comparer_implies_greater_than(q: Seq<int>, key: int, lower_bound: int, upper_bound: int)
    requires
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer(q, key, lower_bound, upper_bound, FnSpec(|n1: int, n2: int| greater_than(n1, n2)))
    ensures
        forall |i: int| lower_bound <= i < upper_bound ==> q[i] > key
{
}

proof fn lemma_sorted_implies_ordering(q: Seq<int>, i: int, j: int)
    requires
        sorted(q),
        0 <= i <= j < q.len()
    ensures
        q[i] <= q[j]
{
}

proof fn lemma_find_range_post_conditions(q: Seq<int>, key: int, left_index: usize, right_index: usize)
    requires
        sorted(q),
        left_index <= right_index <= q.len(),
        forall |i: int| 0 <= i < left_index as int ==> q[i] < key,
        forall |i: int| left_index as int <= i < right_index as int ==> q[i] == key,
        forall |i: int| right_index as int <= i < q.len() as int ==> q[i] > key
    ensures
        left_index <= right_index <= q.len(),
        forall |i: int| 0 <= i < left_index as int ==> q[i] < key,
        forall |i: int| left_index as int <= i < right_index as int ==> q[i] == key,
        forall |i: int| right_index as int <= i < q.len() as int ==> q[i] > key
{
}
// </vc-helpers>

// <vc-spec>
fn find_range(q: Seq<int>, key: int) -> (res: (usize, usize))
    requires sorted(q)
    ensures
        res.0 <= res.1 <= q.len(),
        forall |i: int| 0 <= i < res.0 ==> q[i] < key,
        forall |i: int| res.0 <= i < res.1 ==> q[i] == key,
        forall |i: int| res.1 <= i < q.len() ==> q[i] > key
// </vc-spec>
// <vc-code>
{
    let lower_bound: usize = 0;
    let upper_bound: usize = if q.len() == 0 { 0 } else { q.len() };
    let mut left_index = binary_search(
        q,
        key,
        lower_bound,
        upper_bound,
        FnSpec(|n1: int, n2: int| greater_than_or_equal(n1, n2))
    );
    
    proof {
        lemma_range_satisfies_comparer_negation_implies_less_than(q, key, 0, left_index as int);
        lemma_range_satisfies_comparer_implies_greater_than_or_equal(q, key, left_index as int, q.len() as int);
    }
    
    let mut right_index = binary_search(
        q,
        key, 
        left_index,
        upper_bound,
        FnSpec(|n1: int, n2: int| greater_than(n1, n2))
    );
    
    proof {
        lemma_range_satisfies_comparer_implies_greater_than(q, key, right_index as int, q.len() as int);
        
        assert forall |i: int| 0 <= i < left_index as int implies q[i] < key by {
            assert(q[i] < key);
        };
        
        assert forall |i: int| left_index as int <= i < right_index as int implies q[i] == key by {
            if left_index as int <= i < right_index as int {
                assert(q[i] >= key);
                if i < right_index as int - 1 {
                    lemma_sorted_implies_ordering(q, i, right_index as int - 1);
                    assert(q[i] <= q[right_index as int - 1]);
                }
                if i > left_index as int {
                    lemma_sorted_implies_ordering(q, left_index as int, i);
                    assert(q[left_index as int] <= q[i]);
                }
            }
        };
        
        assert forall |i: int| right_index as int <= i < q.len() as int implies q[i] > key by {
            assert(q[i] > key);
        };
        
        lemma_find_range_post_conditions(q, key, left_index, right_index);
    }
    
    (left_index, right_index)
}
// </vc-code>

fn main() {
}

}