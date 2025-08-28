use vstd::prelude::*;

verus! {

/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

spec fn sorted_between(a: Seq<int>, from: int, to: int) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() && from <= i <= j <= to ==> a[i] <= a[j]
}

spec fn sorted(a: Seq<int>) -> bool {
    sorted_between(a, 0, (a.len() - 1) as int)
}

/* Explanation:

invariant forall n, m :: 0 <= n <= i <m <N ==> A [n] <= A [m]
     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

invariant forall n :: 0 <= n <= j ==> A [n] <= A [j]
     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/

// <vc-helpers>
spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool {
    a.to_multiset() == b.to_multiset()
}

proof fn lemma_sorted_between_insert(a: Seq<int>, from: int, to: int, i: int, val: int)
    requires
        0 <= from <= i <= to < a.len(),
        sorted_between(a, from, to),
        (forall|k: int| from <= k < i ==> a[k] <= val),
        (forall|k: int| i <= k <= to ==> val <= a[k]),
    ensures
        sorted_between(a.insert(i, val), from, to + 1)
{
}

proof fn lemma_sorted_between_subrange(a: Seq<int>, from: int, mid: int, to: int)
    requires
        sorted_between(a, from, to),
        from <= mid <= to,
    ensures
        sorted_between(a, from, mid),
        sorted_between(a, mid, to)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubble_sort(a: &mut Vec<int>)
    ensures 
        sorted(a@),
        a@.to_multiset() == old(a)@.to_multiset()
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bubble_sort(a: &mut Vec<int>)
    ensures
        sorted(a@),
        a@.to_multiset() == old(a)@.to_multiset()
{
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i <= n,
            sorted_between(a@, 0, i as int),
            forall|k: int, m: int| 0 <= k < i && i <= m < n as int ==> a@[k] <= a@[m],
            is_permutation(a@, old(a)@)
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= i < n,
                0 <= j <= n - i - 1,
                sorted_between(a@, 0, i as int),
                forall|k: int, m: int| 0 <= k < i && i <= m < n as int ==> a@[k] <= a@[m],
                forall|k: int| 0 <= k < j ==> a@[k] <= a@[j],
                is_permutation(a@, old(a)@)
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

fn main() {}

}