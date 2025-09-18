// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected the `is_sorted` helper to use `s.len() - 1` as the upper bound for `i` in the loop condition, preventing out-of-bounds access. Refined invariants to ensure correctness of the sorted property up to `i`. */
proof fn is_sorted(s: Seq<i32>) -> (result: bool)
    ensures result <==> (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j])
{
    if s.len() <= 1 {
        return true;
    }
    let mut i: int = 0;
    while i < (s.len() as int) - 1
        invariant
            0 <= i && i < s.len(),
            forall|idx1: int, idx2: int| 0 <= idx1 <= idx2 <= i ==> s[idx1] <= s[idx2]
        decreases (s.len() as int) - 1 - i
    {
        if s[i] > s[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

proof fn is_permutation(s1: Seq<i32>, s2: Seq<i32>) -> (result: bool)
    ensures result <==> s1.to_multiset() == s2.to_multiset()
{
    s1.to_multiset() == s2.to_multiset()
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type mismatches by ensuring that `usize` conversions are applied to `int` values only when accessing `Vec` elements or `Vec` length. Modified `while` loop conditions and array accesses to use appropriate types. Refined `while` loop invariants to reflect the state of the `result` vector correctly at each iteration.*/
{
    let mut result = l;
    let mut i: int = 1;

    while i < result.len() as int
        invariant
            0 <= i && i <= result.len() as int,
            result@.to_multiset() == l@.to_multiset(),
            forall|k: int, m: int| 0 <= k < m && m < i ==> result@[k] <= result@[m]
        decreases (result.len() as int) - i
    {
        let key = result.index(i as usize);
        let mut j: int = i - 1;

        while j >= 0 && result.index(j as usize) > key
            invariant
                -1 <= j && j < i,
                result@.to_multiset() == l@.to_multiset(),
                forall|k: int, m: int| 0 <= k < m && m < (j + 1) ==> result@[k] <= result@[m],
                forall|k: int| j < k && k < i ==> result@[k] > key,
                // Elements from j+1 to i-1 have been shifted right. Original elements are still present. Elements from 0 to j are sorted
            decreases j
        {
            result.set((j + 1) as usize, result.index(j as usize));
            j = j - 1;
        }
        result.set((j + 1) as usize, key);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}