// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn find_substring_at(haystack: Seq<char>, needle: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + needle.len() <= haystack.len() &&
    haystack.subrange(pos, pos + needle.len()) == needle
}

fn find(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && 
        sub.len() == start.len() && 
        start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            0 <= start[i] && 
            start[i] <= end_pos[i] && 
            end_pos[i] < a[i]@.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {

            (result[i] == -1 <==> 
                forall|pos: int| start[i] as int <= pos && pos <= end_pos[i] as int && pos + sub[i]@.len() <= a[i]@.len() ==>
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (result[i] >= 0 ==> 
                start[i] as int <= result[i] as int && 
                result[i] as int <= end_pos[i] as int &&
                result[i] as int + sub[i]@.len() <= a[i]@.len() &&
                find_substring_at(a[i]@, sub[i]@, result[i] as int) &&
                forall|pos: int| start[i] as int <= pos && pos < result[i] as int ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (sub[i]@.len() == 0 ==> result[i] == start[i]) &&

            (start[i] as int + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&

            (start[i] > end_pos[i] ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed unnecessary integer casts from runtime code, replaced `k as int <= current_end_pos as int + 1` with `k <= current_end_pos + 1` in invariant clause to satisfy compilation. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let current_a = a[j]@;
                let current_sub = sub[j]@;
                let current_start_val: int = start[j] as int;
                let current_end_pos_val: int = end_pos[j] as int;
                let found_idx_val: int = result[j] as int;

                (found_idx_val == -1 <==> 
                    forall|pos: int| current_start_val <= pos && pos <= current_end_pos_val && pos + current_sub.len() <= current_a.len() ==> 
                        !find_substring_at(current_a, current_sub, pos)) &&

                (found_idx_val >= 0 ==> 
                    current_start_val <= found_idx_val && 
                    found_idx_val <= current_end_pos_val &&
                    found_idx_val + current_sub.len() <= current_a.len() &&
                    find_substring_at(current_a, current_sub, found_idx_val) &&
                    forall|pos: int| current_start_val <= pos && pos < found_idx_val ==> 
                        !find_substring_at(current_a, current_sub, pos)) &&

                (current_sub.len() == 0 ==> found_idx_val == current_start_val) &&

                (current_start_val + current_sub.len() > current_a.len() ==> found_idx_val == -1) &&

                (current_start_val > current_end_pos_val ==> found_idx_val == -1)
            }
        decreases a.len() - i
    {
        let current_a = a[i]@;
        let current_sub = sub[i]@;
        let current_start: i32 = start[i];
        let current_end_pos: i32 = end_pos[i];

        let mut found_idx: i32 = -1;
        let mut k: i32 = current_start;

        if current_sub.len() == 0 {
             found_idx = current_start;
        } else if current_start as int + current_sub.len() > current_a.len() || current_start > current_end_pos {
            found_idx = -1;
        } else {
            while k <= current_end_pos
                invariant
                    current_start <= k,
                    k <= current_end_pos + 1,
                    found_idx == -1,
                    forall|pos: int| current_start as int <= pos && pos < k as int ==> 
                        !find_substring_at(current_a, current_sub, pos),
                decreases current_end_pos as int - k as int
            {
                if k as int + current_sub.len() <= current_a.len() && find_substring_at(current_a, current_sub, k as int) {
                    found_idx = k;
                    break;
                }
                k = k + 1;
            }
        }

        result.push(found_idx);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}