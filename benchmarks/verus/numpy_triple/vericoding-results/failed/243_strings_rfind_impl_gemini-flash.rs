// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed string_ends_with_suffix_is_empty as it is not used. */
// </vc-helpers>

// <vc-spec>
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>, start_pos: int) -> bool {
    start_pos >= 0 && start_pos + prefix.len() <= s.len() &&
    forall|i: int| 0 <= i < prefix.len() ==> s[start_pos + i] == prefix[i]
}

fn rfind(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < start.len() ==> 0 <= start[i] && start[i] <= end_pos[i],
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            /* Basic range constraint: result is -1 or within string bounds */
            (result[i] == -1 || (0 <= result[i] && result[i] < a[i]@.len())) &&
            /* If result is -1, no occurrence of substring within the specified range */
            (result[i] == -1 ==> 
                forall|j: int| start[i] <= j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                               j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)) &&
            /* If result is non-negative, it's the rightmost valid occurrence */
            (result[i] >= 0 ==> 
                /* The result is within the search range */
                start[i] <= result[i] && 
                result[i] + sub[i]@.len() <= end_pos[i] + 1 &&
                /* The substring matches at this position */
                string_starts_with(a[i]@, sub[i]@, result[i] as int) &&
                /* This is the rightmost occurrence within the range */
                (forall|j: int| result[i] < j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                                start[i] <= j && j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)))
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected type casting errors from `int` to `i32` for concrete variables. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (result[k] == -1 || (0 <= result[k] && result[k] < a[k]@.len())) &&
                (result[k] == -1 ==> forall|j: int| start[k] <= j && j + sub[k]@.len() <= end_pos[k] + 1 && j + sub[k]@.len() <= a[k]@.len() ==> !string_starts_with(a[k]@, sub[k]@, j))) &&
                (result[k] >= 0 ==> (start[k] <= result[k] && result[k] + sub[k]@.len() <= end_pos[k] + 1 && string_starts_with(a[k]@, sub[k]@, result[k] as int) && (forall|j: int| result[k] < j && j + sub[k]@.len() <= end_pos[k] + 1 && start[k] <= j && j + sub[k]@.len() <= a[k]@.len() ==> !string_starts_with(a[k]@, sub[k]@, j))))
            ),
        decreases
            a.len() - i
    {
        let cur_string = a[i]@.clone();
        let cur_sub = sub[i]@.clone();
        let cur_start: i32 = start[i];
        let cur_end_pos: i32 = end_pos[i];

        let mut found_idx: i32 = -1;
        let mut j: i32 = cur_end_pos;

        while j >= cur_start
            invariant
                cur_start <= j && j <= cur_end_pos,
                found_idx == -1 || (
                    cur_start <= found_idx && (found_idx as nat) + cur_sub.len() <= cur_string.len() &&
                    string_starts_with(cur_string, cur_sub, found_idx as int) &&
                    forall|k: int| (j as int) < k && k <= (cur_end_pos as int) && ((k as nat) + cur_sub.len() <= cur_string.len()) ==> !string_starts_with(cur_string, cur_sub, k)
                ),
            decreases
                j - cur_start
        {
            if (j as nat) + cur_sub.len() <= cur_string.len() {
                if string_starts_with(cur_string, cur_sub, j as int) {
                    found_idx = j;
                    break;
                }
            }
            j = j - 1;
        }

        result.push(found_idx);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}