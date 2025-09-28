// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and indexing issues by consistently using `int` for loop counters and `@` for sequence indexing. */
{
    let ghost tracked_s: Seq<int> = l@.map(|i, x: i8| x as int);
    let n: int = tracked_s.len() as int;

    if n < 3 {
        return false;
    }

    let mut i: int = 0;
    while i < n - 2
        invariant
            i >= 0,
            i <= n - 2,
            // All triples (a, b, c) with a < i have been checked and none sum to zero.
            forall|a: int, b: int, c: int| 0 <= a < b < c < n && a < i ==> tracked_s[a] + tracked_s[b] + tracked_s[c] != 0,
        decreases n - i
    {
        let mut j: int = i + 1;
        while j < n - 1
            invariant
                j >= i + 1,
                j <= n - 1,
                // All triples (i, b, c) with b < j have been checked and none sum to zero.
                forall|b: int, c: int| i < b < c < n && b < j ==> tracked_s[i] + tracked_s[b] + tracked_s[c] != 0,
                // Invariant for `i` loop also holds.
                forall|a: int, b: int, c: int| 0 <= a < b < c < n && a < i ==> tracked_s[a] + tracked_s[b] + tracked_s[c] != 0,
            decreases n - j
        {
            let mut k: int = j + 1;
            while k < n
                invariant
                    k >= j + 1,
                    k <= n,
                    // All triples (i, j, c) with c < k have been checked and none sum to zero.
                    forall|c: int| j < c < n && c < k ==> tracked_s[i] + tracked_s[j] + tracked_s[c] != 0,
                    // Invariants for `j` and `i` loops also hold.
                    forall|b: int, c: int| i < b < c < n && b < j ==> tracked_s[i] + tracked_s[b] + tracked_s[c] != 0,
                    forall|a: int, b: int, c: int| 0 <= a < b < c < n && a < i ==> tracked_s[a] + tracked_s[b] + tracked_s[c] != 0,
                decreases n - k
            {
                if tracked_s@[i] + tracked_s@[j] + tracked_s@[k] == 0 {
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    false
}
// </vc-code>


}

fn main() {}