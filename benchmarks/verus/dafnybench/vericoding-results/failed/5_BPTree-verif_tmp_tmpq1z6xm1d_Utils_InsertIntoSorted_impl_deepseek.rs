use vstd::prelude::*;

verus! {

// Function SetLessThan equivalent
spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
    numbers.filter(|i: int| i < threshold)
}

// Function seqSet equivalent
spec fn seq_set(nums: Seq<int>, index: nat) -> Set<int> {
    if index < nums.len() {
        Set::new(|x: int| exists|i: int| 0 <= i < index && i < nums.len() && nums[i] == x)
    } else {
        Set::empty()
    }
}

// Predicate SortedSeq equivalent
spec fn sorted_seq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// Method GetInsertIndex equivalent
fn get_insert_index(a: &[int], limit: usize, x: int) -> (idx: usize)
    requires 
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.take(limit as int)),
    ensures
        idx <= limit,
        sorted_seq(a@.take(limit as int)),
        idx > 0 ==> a[(idx - 1) as int] < x,
        idx < limit ==> x < a[idx as int],
{
    assume(false);
    0
}

// Predicate sorted equivalent
spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// Predicate distinct equivalent
spec fn distinct(a: Seq<int>) -> bool {
    forall|i: int, j: int| (0 <= i < a.len() && 0 <= j < a.len() && i != j) ==> a[i] != a[j]
}

// Predicate sorted_eq equivalent
spec fn sorted_eq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Predicate lessThan equivalent
spec fn less_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] < key
}

// Predicate greaterThan equivalent
spec fn greater_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > key
}

// Predicate greaterEqualThan equivalent
spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] >= key
}

// Function count equivalent
spec fn count(a: Seq<bool>) -> nat
    decreases a.len()
{
    if a.len() == 0 { 
        0nat 
    } else { 
        (if a[0] { 1nat } else { 0nat }) + count(a.drop_first())
    }
}

// <vc-helpers>
spec fn seq_contains<T>(s: Seq<T>, elem: T) -> bool 
    where T: std::cmp::Eq
{
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

proof fn lemma_seq_take_contains<T: std::cmp::Eq>(s: Seq<T>, n: int, elem: T) 
    requires 
        0 <= n <= s.len(),
    ensures
        seq_contains(s.take(n), elem) == (seq_contains(s, elem) && exists|i: int| 0 <= i < n && s[i] == elem)
{
}

proof fn lemma_seq_take_sorted_impl_preserved(s: Seq<int>, n: int, m: int)
    requires
        0 <= n <= s.len(),
        sorted(s.take(m)),
        n <= m,
    ensures
        sorted(s.take(n))
{
}

proof fn lemma_seq_take_append_one(s: Seq<int>, n: int, x: int) 
    requires
        0 <= n <= s.len(),
        n == 0 || s[n-1] < x,
        n < s.len() ==> x < s[n],
    ensures
        sorted(s.take(n).push(x))
{
}

proof fn lemma_vec_extensionality<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        v1@ =~= v2@,
    ensures
        v1 =~= v2
{
}

proof fn lemma_insert_index_properties(a: Seq<int>, limit: int, x: int, idx: int)
    requires
        !a.contains(x),
        limit <= a.len(),
        sorted(a.take(limit)),
        idx <= limit,
        idx > 0 ==> a[idx-1] < x,
        idx < limit ==> x < a[idx],
    ensures
        sorted(a.take(idx).push(x).add(a.drop_first().take(limit - idx))),
        forall|k: int| 0 <= k < idx ==> a.take(idx).push(x).add(a.drop_first().take(limit - idx))[k] == a[k],
        a.take(idx).push(x).add(a.drop_first().take(limit - idx))[idx] == x,
        forall|k: int| idx < k < limit + 1 ==> a.take(idx).push(x).add(a.drop_first().take(limit - idx))[k] == a[k-1]
{
}

proof fn lemma_push_maintains_sorted(sorted_seq: Seq<int>, elem: int)
    requires
        sorted(sorted_seq),
        sorted_seq.len() == 0 || sorted_seq[sorted_seq.len() as int - 1] < elem,
    ensures
        sorted(sorted_seq.push(elem))
{
}

proof fn lemma_concatenation_maintains_sorted(left: Seq<int>, right: Seq<int>)
    requires
        sorted(left),
        sorted(right),
        left.len() == 0 || right.len() == 0 || left[left.len() as int - 1] < right[0],
    ensures
        sorted(left.add(right))
{
}

proof fn lemma_extend_with_zeros_maintains_sorted(sorted_seq: Seq<int>, zeros_count: nat)
    requires
        sorted(sorted_seq),
        sorted_seq.len() == 0 || sorted_seq[sorted_seq.len() as int - 1] > 0,
    ensures
        sorted(sorted_seq.add(Seq::new(zeros_count, |i: int| 0)))
{
}
// </vc-helpers>

// <vc-spec>
fn insert_into_sorted(a: &[int], limit: usize, key: int) -> (b: Vec<int>)
    requires 
        key > 0,
        !a@.contains(key),
        limit < a.len(),
        forall|i: int| 0 <= i < limit ==> a[i] > 0,
        forall|i: int| limit <= i < a.len() ==> a[i] == 0,
        sorted(a@.take(limit as int)),
    ensures
        b.len() == a.len(),
        sorted(b@.take((limit + 1) as int)),
        forall|i: int| limit + 1 <= i < b.len() ==> b[i] == 0,
        forall|i: int| 0 <= i < limit ==> a@.contains(b[i]),
        forall|i: int| 0 <= i < limit + 1 ==> b[i] > 0,
// </vc-spec>
// <vc-code>
{
    let mut b = Vec::<int>::new();
    let mut i: usize = 0;

    while i < limit
        invariant
            i <= limit,
            b.len() == i,
            sorted(b@),
            forall|k: int| 0 <= k < i ==> b@[k] > 0,
            forall|k: int| 0 <= k < i ==> a@.contains(b@[k]),
            i > 0 ==> a@.take(limit as int).contains(b@[i-1]),
    {
        b.push(a[i]);
        i = i + 1;
    }

    let idx = get_insert_index(&b, limit, key);
    
    proof {
        lemma_seq_take_contains(b@, limit as int, key);
    }
    
    let mut result = Vec::<int>::new();
    let mut j: usize = 0;

    while j < idx
        invariant
            j <= idx,
            result.len() == j,
            sorted(result@),
            forall|k: int| 0 <= k < j ==> result@[k] == b@[k],
            forall|k: int| 0 <= k < j ==> result@[k] > 0,
    {
        result.push(b[j]);
        j = j + 1;
    }
    
    result.push(key);
    j = idx;
    
    while j < limit
        invariant
            j >= idx,
            result.len() == j + 1,
            sorted(result@),
            forall|k: int| 0 <= k < idx ==> result@[k] == b@[k],
            result@[idx] == key,
            forall|k: int| idx < k <= j ==> result@[k] == b@[k-1],
            forall|k: int| 0 <= k <= j ==> result@[k] > 0,
    {
        result.push(b[j]);
        j = j + 1;
    }
    
    let zeros_count = a.len() - (limit + 1);
    let mut k: usize = 0;
    
    while k < zeros_count
        invariant
            k <= zeros_count,
            result.len() == limit + 1 + k,
            sorted(result@),
            forall|m: int| 0 <= m < limit + 1 ==> result@[m] > 0,
            forall|m: int| limit + 1 <= m < result.len() ==> result@[m] == 0,
            forall|m: int| 0 <= m < limit ==> a@.contains(result@[m]),
    {
        result.push(0);
        k = k + 1;
    }

    proof {
        lemma_vec_extensionality(result, result);
    }
    
    result
}
// </vc-code>

fn main() {}

}