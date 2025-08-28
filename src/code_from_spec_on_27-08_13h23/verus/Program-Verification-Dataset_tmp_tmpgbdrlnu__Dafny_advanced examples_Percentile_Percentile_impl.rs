use vstd::prelude::*;

verus! {

// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn sum_upto(a: Seq<int>, end: int) -> int
    decreases end + 2
{
    if end < 0 {
        0
    } else if end >= a.len() {
        0  // out of bounds
    } else {
        a[end] + sum_upto(a, end - 1)
    }
}

spec fn sum(a: Seq<int>) -> int {
    sum_upto(a, a.len() - 1)
}

// <vc-helpers>
proof fn sum_upto_non_negative(a: Seq<int>, end: int)
    requires
        forall|idx: int| 0 <= idx <= end && idx < a.len() ==> a[idx] > 0,
        0 <= end < a.len(),
    ensures
        sum_upto(a, end) > 0
    decreases end + 2
{
    if end < 0 {
        return;
    } else if end >= a.len() {
        return;
    } else {
        if end > 0 {
            sum_upto_non_negative(a, end - 1);
        }
        assert(sum_upto(a, end) == a[end] + sum_upto(a, end - 1));
        assert(a[end] > 0);
        assert(sum_upto(a, end) > 0);
    }
}

proof fn sum_upto_strictly_increasing(a: Seq<int>, i: int)
    requires
        forall|idx: int| 0 <= idx < a.len() ==> a[idx] > 0,
        0 <= i < a.len() - 1,
    ensures
        sum_upto(a, i) < sum_upto(a, i + 1)
    decreases i + 2
{
    sum_upto_non_negative(a, i);
    sum_upto_non_negative(a, i + 1);
    assert(sum_upto(a, i + 1) == a[i + 1] + sum_upto(a, i));
    assert(a[i + 1] > 0);
    assert(sum_upto(a, i + 1) > sum_upto(a, i));
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn percentile(p: int, a: &[int], total: int) -> (i: i32)
    requires 
        forall|idx: int| 0 <= idx < a.len() ==> a@[idx] > 0,
        0 <= p <= 100,
        total == sum(a@),
        total > 0,
    ensures 
        -1 <= i < a.len(),
        sum_upto(a@, i as int) <= (p * total) / 100,
        i as int + 1 < a.len() ==> sum_upto(a@, i as int + 1) > (p * total) / 100,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn percentile(p: int, a: &[int], total: int) -> (i: i32)
    requires 
        forall|idx: int| 0 <= idx < a.len() ==> a@[idx] > 0,
        0 <= p <= 100,
        total == sum(a@),
        total > 0,
    ensures 
        -1 <= i < a.len() as i32,
        sum_upto(a@, i as int) <= (p * total) / 100,
        (i as int + 1) < a.len() ==> sum_upto(a@, i as int + 1) > (p * total) / 100,
{
    let target: int = (p * total) / 100;
    let mut current_sum: int = 0;
    let mut i: i32 = -1;
    let mut index: usize = 0;

    while index < a.len()
        invariant
            0 <= index <= a.len(),
            i as int == index as int - 1,
            -1 <= i < a.len() as i32,
            current_sum == sum_upto(a@, i as int),
            current_sum <= target ==> index < a.len() ==> sum_upto(a@, index as int) > target,
    {
        if current_sum > target {
            break;
        }
        i = index as i32;
        if index < a.len() {
            current_sum = current_sum + a[index];
            proof {
                if index < a.len() - 1 {
                    sum_upto_strictly_increasing(a@, index as int);
                }
            }
        }
        index = index + 1;
    }

    i
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right

fn main() {
}

}