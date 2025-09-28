use vstd::prelude::*;

verus! {

spec fn verify_neg(a: &[int], idx: int) -> nat
    decreases idx
{
    if idx <= 0 {
        0nat
    } else {
        verify_neg(a, idx - 1) + (if a[idx - 1] < 0 { 1nat } else { 0nat })
    }
}

// <vc-helpers>
spec fn sum_neg(a: Seq<int>, from: int, to: int) -> nat
    recommends from <= to
    decreases to - from
{
    if from >= to {
        0nat
    } else {
        (if a[from] < 0 { 1nat } else { 0nat }) + sum_neg(a, from + 1, to)
    }
}

proof fn verify_neg_equals_sum_neg(a: Seq<int>, idx: int)
    ensures verify_neg(a, idx) == sum_neg(a, 0, idx)
    decreases idx
{
    if idx > 0 {
        verify_neg_equals_sum_neg(a, idx - 1);
    }
}

spec fn verify_neg_slice(a: Seq<int>, start: int, end: int) -> nat
    recommends start <= end
    decreases end - start
{
    if start >= end {
        0nat
    } else {
        verify_neg_slice(a, start, end - 1) + (if a[end - 1] < 0 { 1nat } else { 0nat })
    }
}

proof fn verify_neg_slice_equals_sum_neg(a: Seq<int>, start: int, end: int)
    ensures verify_neg_slice(a, start, end) == sum_neg(a, start, end)
    decreases end - start
{
    if start < end {
        verify_neg_slice_equals_sum_neg(a, start, end - 1);
    }
}

proof fn verify_neg_slice_equals_verify_neg(a: Seq<int>, len: int)
    ensures verify_neg_slice(a, 0, len) == verify_neg(a, len)
{
    verify_neg_equals_sum_neg(a, len);
    verify_neg_slice_equals_sum_neg(a, 0, len);
}
// </vc-helpers>

// <vc-spec>
fn count_neg(a: &[int]) -> (cnt: usize)
    ensures cnt == verify_neg(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            cnt == verify_neg_slice(a@, 0, i as int),
        decreases len - i
    {
        proof {
            verify_neg_slice_equals_sum_neg(a@, 0, i as int);
        }
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
        if i <= len {
            proof {
                verify_neg_slice_equals_sum_neg(a@, 0, i as int);
            }
        }
    }
    proof {
        verify_neg_slice_equals_verify_neg(a@, len as int);
    }
    cnt
}
// </vc-code>

fn main() {
}

}