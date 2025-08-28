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
spec fn sorted_up_to(a: Seq<int>, end: int) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() && i <= end && j <= end ==> a[i] <= a[j]
}

spec fn max_in_range(a: Seq<int>, start: int, end: int) -> bool 
    requires 0 <= start <= end < a.len()
{
    forall|k: int| start <= k <= end ==> a[k] <= a[end]
}

lemma lemma_bubble_preserves_sorted(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 
        0 <= i < j < a.len(),
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        b[i] == a[j],
        b[j] == a[i],
        sorted_up_to(a, i - 1),
        a[i] > a[j]
    ensures sorted_up_to(b, i)
{
}

lemma lemma_max_bubble(a: Seq<int>, b: Seq<int>, start: int, end: int)
    requires 
        0 <= start <= end < a.len(),
        a.len() == b.len(),
        forall|k: int| start <= k < end ==> (
            if a[k] > a[k + 1] {
                b[k] == a[k + 1] && b[k + 1] == a[k]
            } else {
                b[k] == a[k] && b[k + 1] == a[k + 1]
            }
        ),
        forall|k: int| 0 <= k < a.len() && (k < start || k > end) ==> a[k] == b[k]
    ensures max_in_range(b, start, end)
{
}

lemma lemma_sorted_extension(a: Seq<int>, i: int)
    requires 
        0 <= i < a.len(),
        sorted_up_to(a, i - 1),
        forall|k: int| 0 <= k <= i - 1 ==> a[k] <= a[i]
    ensures sorted_up_to(a, i)
{
}

lemma lemma_bubble_step(a: Seq<int>, b: Seq<int>, j: int, n: int, i: int)
    requires 
        0 <= j < n - i - 1,
        0 <= i < n,
        n == a.len() == b.len(),
        j + 1 < a.len(),
        a[j] > a[j + 1],
        forall|k: int| 0 <= k < a.len() && k != j && k != (j + 1) ==> a[k] == b[k],
        b[j] == a[j + 1],
        b[j + 1] == a[j],
        forall|k: int| 0 <= k < j ==> a[k] <= a[j + 1]
    ensures forall|k: int| 0 <= k < j ==> b[k] <= b[j]
{
}

lemma lemma_inner_loop_establishes_max(a_orig: Seq<int>, a_final: Seq<int>, n: int, i: int)
    requires
        0 <= i < n,
        n == a_orig.len() == a_final.len(),
        a_orig.to_multiset() == a_final.to_multiset()
    ensures forall|k: int| 0 <= k < n - i - 1 ==> a_final[k] <= a_final[n - i - 1]
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
{
    let n = a.len();
    if n <= 1 {
        return;
    }
    
    for i in 0..n
        invariant
            sorted_up_to(a@, (i as int) - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int, m: int| 0 <= k < i && i <= m < n ==> a@[k] <= a@[m]
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                0 <= j <= n - i - 1,
                sorted_up_to(a@, (i as int) - 1),
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: int| 0 <= k < j ==> a@[k] <= a@[j],
                forall|k: int, m: int| 0 <= k < i && i <= m < n ==> a@[k] <= a@[m]
        {
            if a[j] > a[j + 1] {
                let old_seq = a@;
                a.swap(j, j + 1);
                
                proof {
                    assert(a@.to_multiset() =~= old_seq.to_multiset());
                    if j > 0 {
                        lemma_bubble_step(old_seq, a@, j, n, i);
                    }
                }
            }
            j += 1;
        }
        
        proof {
            if i > 0 {
                lemma_inner_loop_establishes_max(old(a)@, a@, n, i);
                assert(forall|k: int| 0 <= k <= (i as int) - 1 ==> a@[k] <= a@[i as int]);
                lemma_sorted_extension(a@, i as int);
            }
        }
    }
}
// </vc-code>

fn main() {}

}