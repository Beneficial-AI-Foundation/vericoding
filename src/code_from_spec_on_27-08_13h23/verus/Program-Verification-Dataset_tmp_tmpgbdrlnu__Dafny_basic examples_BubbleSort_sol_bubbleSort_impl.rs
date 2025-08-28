use vstd::prelude::*;

verus! {

spec fn sorted_between(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends
        from <= to,
        to <= a.len(),
{
    forall|i: int, j: int| from <= i < j < to && 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] <= a@[j]
}

spec fn sorted(a: &Vec<i32>) -> bool {
    sorted_between(a, 0, a.len())
}

// <vc-helpers>
proof fn lemma_sorted_between_subrange(a: &Vec<i32>, from: usize, to: usize, sub_from: usize, sub_to: usize)
    requires
        from <= sub_from <= sub_to <= to <= a.len(),
        sorted_between(a, from, to),
    ensures
        sorted_between(a, sub_from, sub_to),
{
    assert forall|i: int, j: int| sub_from <= i < j < sub_to && 0 <= i < a.len() && 0 <= j < a.len() implies a@[i] <= a@[j] by {
        assert(from <= i < j < to);
    }
}

proof fn lemma_sorted_between_one_less(a: &Vec<i32>, from: usize, to: usize, idx: usize)
    requires
        from <= idx < to <= a.len(),
        sorted_between(a, from, to),
    ensures
        forall|k: int| from <= k < idx && 0 <= k < a.len() ==> a@[k] <= a@[idx],
        forall|k: int| idx < k < to && 0 <= k < a.len() ==> a@[idx] <= a@[k],
{
    assert forall|k: int| from <= k < idx && 0 <= k < a.len() implies a@[k] <= a@[idx] by {
        assert(from <= k < idx < to);
    }
    assert forall|k: int| idx < k < to && 0 <= k < a.len() implies a@[idx] <= a@[k] by {
        assert(from <= idx < k < to);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubbleSort(a: &mut Vec<i32>)
    requires
        old(a).len() > 0,
    ensures
        sorted(a),
        old(a)@ == a@,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bubble_sort(a: &mut Vec<i32>)
    requires
        old(a).len() > 0,
    ensures
        sorted(a),
        old(a)@.len() == a@.len(),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted_between(a, 0, i),
            forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < n && 0 <= k1 < a.len() && 0 <= k2 < a.len() ==> a@[k1] <= a@[k2],
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= i < n,
                0 <= j <= n - i - 1,
                sorted_between(a, 0, i),
                forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < n && 0 <= k1 < a.len() && 0 <= k2 < a.len() ==> a@[k1] <= a@[k2],
                forall|k: int| 0 <= k < j && 0 <= k < a.len() ==> a@[k] <= a@[(k + 1) as int],
        {
            if a[j] > a[j + 1] {
                a.swap(j, j + 1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}