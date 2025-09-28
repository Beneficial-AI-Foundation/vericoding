// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors by ensuring all array indices are `usize` when used for concrete array access. Replaced `as int` casts for `j` in the while loop condition and predicate checks with `j as usize` where appropriate outside of spec blocks, or removed casts when comparison could be done directly with `usize` or `int` within a spec context. */
fn sort_seq_inner(s: Vec<i8>, p: Vec<bool>, start: int, end: int) -> Vec<i8>
    requires
        0 <= start <= end <= s.len(),
        s.len() == p.len(),
    ensures
        // The sorted part has its elements sorted according to p:
        forall|i: int, j: int| start <= i < j < end && p[i as int] && p[j as int] ==> sort_seq_inner(s, p, start, end)[i] as int <= sort_seq_inner(s, p, start, end)[j] as int,
        // The elements not marked by p are unchanged:
        forall|i: int| start <= i < end && !p[i as int] ==> sort_seq_inner(s, p, start, end)[i] == s[i],
        // The multiset of the entire sequence remains the same
        s@.to_multiset() == sort_seq_inner(s, p, start, end)@.to_multiset(),
{
    let mut arr = s;
    if start < end {
        let pivot_val: i8 = arr[(end - 1) as usize];
        let mut i: usize = start as usize;
        let mut j: usize = start as usize;

        while j < end as usize - 1
            invariant
                start <= i as int <= j as int + 1 <= end,
                arr.len() == s.len(),
                s.len() == p.len(), // Maintaining the property across iterations
                // Elements before i (marked by p and <= pivot) or not marked by p and unchanged
                forall|k: int| start <= k < i as int && p[k as int] ==> arr[k as usize] as int <= pivot_val as int,
                forall|k: int| start <= k < i as int && !p[k as int] ==> arr[k as usize] == s[k as usize],
                // Elements between i and j (marked by p and > pivot) or not marked by p and unchanged
                forall|k: int| i as int <= k < j as int && p[k as int] ==> arr[k as usize] as int > pivot_val as int,
                forall|k: int| i as int <= k < j as int && !p[k as int] ==> arr[k as usize] == s[k as usize],
                arr@.to_multiset() == s@.to_multiset(), // The multiset of arr is always equal to s
        {
            if p[j as usize] {
                if arr[j as usize] as int <= pivot_val as int {
                    if i != j {
                        let temp = arr[i as usize];
                        arr.set(i as usize, arr[j as usize]);
                        arr.set(j as usize, temp);
                    }
                    i = i + 1;
                }
            }
            j = j + 1;
        }

        if p[(end - 1) as usize] {
            if i as int != end - 1 {
                let temp = arr[i as usize];
                arr.set(i as usize, arr[(end - 1) as usize]);
                arr.set((end - 1) as usize, temp);
            }
        }

        arr = sort_seq_inner(arr, p, start, i as int);
        arr = sort_seq_inner(arr, p, i as int + 1, end);
    }
    arr
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i as int] && p[j as int] ==> sorted[i] as int <= sorted[j] as int,
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i as int] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes other than formatting, as helper compilation was the issue. */
{
    let result = sort_seq_inner(s, p, 0, s.len());
    result
}
// </vc-code>


}

fn main() {}