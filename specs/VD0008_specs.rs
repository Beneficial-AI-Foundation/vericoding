// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
    numbers.filter(|i: int| i < threshold)
}

spec fn seq_set(nums: Seq<int>, index: nat) -> Set<int> 
    recommends index <= nums.len()
{
    Set::new(|x: int| exists |i: int| 0 <= i < index && i < nums.len() && nums[i] == x)
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

spec fn sorted(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

spec fn distinct(a: Seq<int>) -> bool {
    forall |i: int, j: int| (0 <= i < a.len() && 0 <= j < a.len() && i != j) ==> a[i] != a[j]
}

spec fn sorted_eq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn less_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] < key
}

spec fn greater_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] > key
}

spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
    forall |i: int| 0 <= i < a.len() ==> a[i] >= key
}

spec fn count(a: Seq<bool>) -> nat 
    decreases a.len()
{
    if a.len() == 0 {
        0nat
    } else {
        (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
    }
}

fn insert_into_sorted(a: Vec<int>, limit: usize, key: int) -> (b: Vec<int>)
    requires
        key > 0,
        !a@.contains(key),
        limit < a.len(),
        forall |i: int| 0 <= i < limit ==> a@[i] > 0,
        forall |i: int| limit <= i < a.len() ==> a@[i] == 0,
        sorted(a@.subrange(0, limit as int)),
    ensures
        b.len() == a.len(),
        sorted(b@.subrange(0, limit as int + 1)),
        forall |i: int| limit + 1 <= i < b.len() ==> b@[i] == 0,
        forall |i: int| 0 <= i < limit ==> a@.contains(b@[i]),
        forall |i: int| 0 <= i < limit + 1 ==> b@[i] > 0,
{
    assume(false);
    Vec::new()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_insert_index(a: &Vec<int>, limit: usize, x: int) -> (idx: usize)

    requires
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.subrange(0, limit as int)),
    ensures
        idx <= limit,
        sorted_seq(a@.subrange(0, limit as int)),
        idx > 0 ==> a@[idx as int - 1] < x,
        idx < limit ==> x < a@[idx as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}