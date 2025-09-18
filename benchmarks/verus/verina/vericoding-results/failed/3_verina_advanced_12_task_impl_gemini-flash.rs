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
/* code modified by LLM (iteration 5): Corrected type mismatches by casting `lst.len()` to `int` for sequence indexing and ensuring `seen` map keys match `lst` element types. Updated iterators for quantifiers to `int` and used `@` for sequence indexing as a value type instead of reference. */
{
    let len: int = lst.len() as int;
    let mut seen: Map<i32, int> = Map::empty();
    let mut first_dup_val: i32 = -1;
    let mut min_j: int = len;
    let mut min_i: int = len;

    let mut j: int = 0;
    while j < len
        invariant
            0 <= j && j <= len,
            forall|idx: int| 0 <= idx < j ==> {
                seen.contains_key(lst@idx) ==> seen[lst@idx] < idx && seen[lst@idx] <= idx
            },
            // min_j is the smallest index such that there's a duplicate pair (min_i, min_j)
            // and first_dup_val is lst[min_i]
            (first_dup_val == -1 ==> forall|x: int, y: int| 0 <= x < y < j ==> lst@x != lst@y),
            (first_dup_val != -1 ==> exists|x: int, y: int| 0 <= x < y < j && lst@x == lst@y && lst@x == first_dup_val && y == min_j && x == min_i),
            (first_dup_val != -1 ==> forall|x: int, y: int| 0 <= x < y < j && lst@x == lst@y ==> y >= min_j),
            (first_dup_val != -1 ==> forall|x: int, y: int| 0 <= x < y < j && lst@x == lst@y && y == min_j ==> x >= min_i)
        decreases len - j
    {
        let current_val = lst@j;
        if seen.contains_key(current_val) {
            let i = seen[current_val];
            if first_dup_val == -1 || j < min_j {
                first_dup_val = current_val;
                min_j = j;
                min_i = i;
            } else if j == min_j {
                if i < min_i {
                    min_i = i;
                }
            }
        } else {
            seen = seen.insert(current_val, j);
        }
        j = j + 1;
    }

    first_dup_val
}
// </vc-code>

}
fn main() {}