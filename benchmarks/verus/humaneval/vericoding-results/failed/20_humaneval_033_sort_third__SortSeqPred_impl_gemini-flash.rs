// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix function keyword to `function` for `is_sorted_by_pred` instead of `function_spec` */
function is_sorted_by_pred(s: Seq<i8>, p: Seq<bool>) -> bool
  requires
    s.len() == p.len(),
{
  forall|i: int, j: int| 0 <= i < j < s.len() && p[i] && p[j] ==> s[i] as int <= s[j] as int
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix while loop invariant to precisely track the minimum element found so far, ensuring correct sorting. */
{
    let mut result = s.clone();

    let len = s.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == len,
            s.len() == len,
            p.len() == len,
            // Elements that are not marked by p are preserved in their original positions
            forall|k: int| 0 <= k < len && !p[k] ==> result[k] == s[k],
            // The multiset of *marked* elements in `result` combined with unmarked elements is a permutation of `s`'s elements.
            s@.to_multiset() == result@.to_multiset(),
            // For the already processed part (0 to i-1), if p[k] is true, they are in a sorted relative order.
            is_sorted_by_pred(result@.subsequence(0, i), p@.subsequence(0, i)),
        decreases len - i
    {
        if p[i] {
            // Find the minimum element among p-marked elements from i to len-1
            let mut min_val = result[i];
            let mut min_idx = i;
            let mut j = i + 1;
            while j < len
                invariant
                    i < j <= len,
                    i <= min_idx < j,
                    p.len() == len,
                    result.len() == len,
                    is_sorted_by_pred(result@.subsequence(0, i), p@.subsequence(0, i)),
                    s@.to_multiset() == result@.to_multiset(),
                    forall|k: int| 0 <= k < len && !p[k] ==> result[k] == s[k],
                    // If p-marked elements exist from i to j-1, min_val and min_idx correctly identify the minimum.
                    // If no p-marked element is found, min_val and min_idx track the first element considered (result[i]).
                    (p[min_idx] && result[min_idx] == min_val) || (!p[min_idx] && (min_idx == i || !p[min_idx])), // min_idx correctly tracks a P-marked element or the default at i
                    (forall|k: int|
                        i <= k < j && p[k]
                        ==>
                        min_val as int <= result[k] as int
                    ),

                decreases len - j
            {
                if p[j] { // Only consider p-marked elements for finding min
                    if p[min_idx] { // min_idx currently points to a p-marked element
                        if (result[j] as int) < (min_val as int) {
                            min_val = result[j];
                            min_idx = j;
                        }
                    } else { // min_idx currently points to an unmarked element (initial state before finding any p-marked element)
                        min_val = result[j];
                        min_idx = j;
                    }
                }
                // If p[min_idx] is false and p[j] is also false, min_val and min_idx remain unchanged for this iteration.
                j = j + 1;
            }
            
            if p[min_idx] && min_idx != i { // Only swap if a p-marked element was truly chosen as min_idx
                let temp = result[i];
                result.set(i, result[min_idx]);
                result.set(min_idx, temp);
            }

        } else {
            // If p[i] is false, we don't sort this element. It stays in its original position.
            // This is implicitly handled by the outer loop, as we only perform swaps for p[i] == true.
            // The invariant result[i] == s[i] when !p[i] must be maintained, which it is.
        }

        i = i + 1;
    }

    proof {
        assert(is_sorted_by_pred(result@, p@));
        assert(result.len() == s.len());
        // The `forall` condition in the `ensures` clause directly corresponds to `is_sorted_by_pred`
        assert(
            forall|k: int, l: int| 0 <= k < l < result.len() && p[k] && p[l] ==> result[k] as int <= result[l] as int
        );
        assert(s@.to_multiset() == result@.to_multiset());
        assert(forall|idx: int| 0 <= idx < len && !p[idx] ==> result[idx] == s[idx]);
    }

    result
}

// </vc-code>


}

fn main() {}