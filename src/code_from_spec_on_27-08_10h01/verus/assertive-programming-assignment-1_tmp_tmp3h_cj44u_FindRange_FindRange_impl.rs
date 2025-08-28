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
spec fn ge_comparer(n1: int, n2: int) -> bool {
    n1 >= n2
}

spec fn gt_comparer(n1: int, n2: int) -> bool {
    n1 > n2
}

proof fn lemma_comparer_gt_properties(q: Seq<int>, key: int, lower: int, upper: int)
    requires 
        0 <= lower <= upper <= q.len(),
        sorted(q)
    ensures
        range_satisfies_comparer_negation(q, key, 0, lower, FnSpec::new(gt_comparer)) 
            <==> (forall |i: int| 0 <= i < lower ==> q[i] <= key),
        range_satisfies_comparer(q, key, upper, q.len() as int, FnSpec::new(gt_comparer))
            <==> (forall |i: int| upper <= i < q.len() ==> q[i] > key)
{
}

proof fn lemma_comparer_ge_properties(q: Seq<int>, key: int, lower: int, upper: int)
    requires 
        0 <= lower <= upper <= q.len(),
        sorted(q)
    ensures
        range_satisfies_comparer_negation(q, key, 0, lower, FnSpec::new(ge_comparer))
            <==> (forall |i: int| 0 <= i < lower ==> q[i] < key),
        range_satisfies_comparer(q, key, upper, q.len() as int, FnSpec::new(ge_comparer))
            <==> (forall |i: int| upper <= i < q.len() ==> q[i] >= key)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_range(q: Seq<int>, key: int) -> (res: (usize, usize))
    requires sorted(q)
    ensures
        res.0 <= res.1 <= q.len(),
        forall |i: int| 0 <= i < res.0 ==> q[i] < key,
        forall |i: int| res.0 <= i < res.1 ==> q[i] == key,
        forall |i: int| res.1 <= i < q.len() ==> q[i] > key
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        lemma_comparer_ge_properties(q, key, 0, q.len() as int);
        lemma_comparer_gt_properties(q, key, 0, q.len() as int);
    }
    
    let left = binary_search(q, key, 0, q.len(), FnSpec::new(ge_comparer));
    
    proof {
        lemma_comparer_gt_properties(q, key, left as int, q.len() as int);
    }
    
    let right = binary_search(q, key, left, q.len(), FnSpec::new(gt_comparer));
    
    (left, right)
}
// </vc-code>

fn main() {
}

}