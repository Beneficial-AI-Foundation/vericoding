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
proof fn lemma_comparer_gt_properties(q: Seq<int>, key: int, lower_bound: int, upper_bound: int)
    requires
        sorted(q),
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, 0int, lower_bound, |n1: int, n2: int| n1 > n2),
        range_satisfies_comparer(q, key, upper_bound, q.len() as int, |n1: int, n2: int| n1 > n2)
    ensures
        forall |i: int| 0 <= i < lower_bound ==> q[i] <= key,
        forall |i: int| upper_bound <= i < q.len() ==> q[i] > key
{
    assert(forall |i: int| 0 <= i < lower_bound ==> !(q[i] > key));
    assert(forall |i: int| upper_bound <= i < q.len() ==> q[i] > key);
}

proof fn lemma_comparer_ge_properties(q: Seq<int>, key: int, lower_bound: int, upper_bound: int)
    requires
        sorted(q),
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, 0int, lower_bound, |n1: int, n2: int| n1 >= n2),
        range_satisfies_comparer(q, key, upper_bound, q.len() as int, |n1: int, n2: int| n1 >= n2)
    ensures
        forall |i: int| 0 <= i < lower_bound ==> q[i] < key,
        forall |i: int| upper_bound <= i < q.len() ==> q[i] >= key
{
    assert(forall |i: int| 0 <= i < lower_bound ==> !(q[i] >= key));
    assert(forall |i: int| upper_bound <= i < q.len() ==> q[i] >= key);
}

spec fn gt_comparer_spec() -> spec_fn(int, int) -> bool {
    |n1: int, n2: int| n1 > n2
}

spec fn ge_comparer_spec() -> spec_fn(int, int) -> bool {
    |n1: int, n2: int| n1 >= n2
}

proof fn lemma_gt_comparer_properties()
    ensures forall |n1: int, n2: int| #[trigger] gt_comparer_spec()(n1, n2) == (n1 > n2)
{
}

proof fn lemma_ge_comparer_properties()
    ensures forall |n1: int, n2: int| #[trigger] ge_comparer_spec()(n1, n2) == (n1 >= n2)
{
}

proof fn lemma_initial_conditions_gt(q: Seq<int>, key: int)
    requires sorted(q)
    ensures 
        range_satisfies_comparer_negation(q, key, 0int, 0int, gt_comparer_spec()),
        range_satisfies_comparer(q, key, q.len() as int, q.len() as int, gt_comparer_spec())
{
}

proof fn lemma_initial_conditions_ge(q: Seq<int>, key: int)
    requires sorted(q)
    ensures 
        range_satisfies_comparer_negation(q, key, 0int, 0int, ge_comparer_spec()),
        range_satisfies_comparer(q, key, q.len() as int, q.len() as int, ge_comparer_spec())
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
    proof {
        lemma_gt_comparer_properties();
        lemma_initial_conditions_gt(q, key);
    }
    
    let q_len = q.len() as usize;
    
    let left_bound = binary_search(q, key, 0, q_len, gt_comparer_spec());
    
    proof {
        lemma_comparer_gt_properties(q, key, left_bound as int, q.len() as int);
        lemma_ge_comparer_properties();
        lemma_initial_conditions_ge(q, key);
    }
    
    let right_bound = binary_search(q, key, 0, q_len, ge_comparer_spec());
    
    proof {
        lemma_comparer_ge_properties(q, key, right_bound as int, q.len() as int);
    }
    
    (left_bound, right_bound)
}
// </vc-code>

fn main() {
}

}