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
    let mut idx = 0;
    let mut i = 0;
    
    while i < limit
        invariant
            0 <= idx <= i <= limit,
            sorted_seq(a@.take(limit as int)),
            forall|j: int| 0 <= j < idx ==> a[j] < x,
            forall|j: int| idx <= j < i ==> x < a[j],
    {
        if a[i] < x {
            idx = i + 1;
        } else {
            break;
        }
        i += 1;
    }
    
    idx
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
    let mut b = Vec::new();
    if let Err(_) = b.extend_with(a.len(), |i| a[i]) {
        return Vec::new();
    }
    
    let idx = get_insert_index(a, limit, key);
    
    for i in (idx..limit).rev()
        invariant 
            idx <= i + 1 <= limit,
            forall|j: int| 0 <= j < b.len() ==> 
                (j < idx || j > i ==> b[j] == a@[j]),
            forall|j: int| idx <= j <= i ==> b[j] == a@[j - 1],
            sorted(b@.take((limit + 1) as int)),
            forall|j: int| 0 <= j < limit ==> b@.contains(a@[j]),
            forall|j: int| 0 <= j <= limit ==> b[j] > 0 ==> (j != idx ==> b[j] == a@[j - (j > idx as int) as int]),
            forall|j: int| limit <= j < b.len() ==> b[j] == 0,
    {
        b[i + 1] = b[i];
    }
    
    b[idx] = key;
    
    b
}
// </vc-code>

fn main() {}

}