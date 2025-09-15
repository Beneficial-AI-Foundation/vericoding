// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn first_duplicate(lst: &Seq<i32>) -> (result: i32)
    ensures

        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&

        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix compilation errors related to `int` and `Seq` indexing */
{
    let mut seen: vstd::map::Map<i32, bool> = vstd::map::Map::empty();
    let mut min_duplicate_value: i32 = -1;
    let mut min_duplicate_index: usize = 0; // Changed to usize

    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i && i <= lst.len(),
            seen.dom().subset_of(lst.to_set()),
            min_duplicate_value == -1 ==> (forall|k: int, l: int| 0 <= k < l < i as int ==> lst[k as usize] != lst[l as usize]),
            min_duplicate_value != -1 ==> (
                exists|k: int, l: int| 0 <= k < l < i as int && lst[k as usize] == lst[l as usize] && lst[k as usize] == min_duplicate_value &&
                forall|x: int, y: int| 0 <= x < y < i as int && lst[x as usize] == lst[y as usize] ==> y >= min_duplicate_index as int
            ),
            // min_duplicate_index == 0 || ( // Removed this line and updated the one below
            (min_duplicate_index == 0 && min_duplicate_value == -1) || (min_duplicate_index < i && min_duplicate_value != -1
                && exists|k: int| 0 <= k < min_duplicate_index as int && lst[k as usize] == min_duplicate_value && lst[min_duplicate_index] == min_duplicate_value
            )
    {
        let current_val = lst.index(i);
        if seen.contains_key(current_val) {
            if min_duplicate_value == -1 || i < min_duplicate_index {
                // Determine the first occurrence of current_val
                let mut first_occurrence_idx: usize = 0;
                while first_occurrence_idx < i
                    invariant
                        0 <= first_occurrence_idx && first_occurrence_idx <= i,
                        (forall|k: usize| 0 <= k && k < first_occurrence_idx ==> lst.index(k) != current_val)
                    decreases i - first_occurrence_idx
                {
                    if lst.index(first_occurrence_idx) == current_val {
                        break;
                    }
                    first_occurrence_idx = first_occurrence_idx + 1;
                }

                if min_duplicate_value == -1 || i < min_duplicate_index {
                    min_duplicate_value = current_val;
                    min_duplicate_index = i;
                }
            }
        } else {
            seen = seen.insert(current_val, true);
        }
        i = i + 1;
    }
    min_duplicate_value
}
// </vc-code>

}
fn main() {}