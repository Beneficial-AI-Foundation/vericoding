// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Correct `subrange` argument type from `nat` to `int`. */
proof fn substring_length_positive(s: Seq<char>) ensures s.len() >= 0 { } 
spec fn is_prefix(s1: Seq<char>, s2: Seq<char>) -> bool {
    s1.len() as int <= s2.len() as int && s2.subrange(0, s1.len() as int) == s1
}

proof fn substring_implies_length_range(haystack: Seq<char>, needle: Seq<char>, pos: int)
    requires 
        pos >= 0,
        find_substring_at(haystack, needle, pos)
    ensures 
        pos + needle.len() <= haystack.len()
{ }
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
                forall|pos: int| start[i] <= pos && pos <= end_pos[i] && pos + sub[i]@.len() <= a[i]@.len() ==>
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (result[i] >= 0 ==> 
                start[i] <= result[i] && 
                result[i] <= end_pos[i] &&
                result[i] + sub[i]@.len() <= a[i]@.len() &&
                find_substring_at(a[i]@, sub[i]@, result[i] as int) &&
                forall|pos: int| start[i] <= pos && pos < result[i] ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (sub[i]@.len() == 0 ==> result[i] == start[i]) &&

            (start[i] + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&

            (start[i] > end_pos[i] ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors related to `int` and `usize` type mismatches for indexing and iteration, and cast issues. */
{
    let mut result_vec = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant 
            0 <= i as int && i as int <= a.len() as int,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                (result_vec[j] == -1 <==> 
                    forall|pos: int| start[j as usize] <= pos && pos <= end_pos[j as usize] && pos + sub[j as usize]@.len() <= a[j as usize]@.len() ==> 
                        !find_substring_at(a[j as usize]@, sub[j as usize]@, pos)) &&

                (result_vec[j] >= 0 ==> 
                    start[j as usize] <= result_vec[j] && 
                    result_vec[j] <= end_pos[j as usize] &&
                    result_vec[j] + sub[j as usize]@.len() <= a[j as usize]@.len() &&
                    find_substring_at(a[j as usize]@, sub[j as usize]@, result_vec[j] as int) &&
                    forall|pos: int| start[j as usize] <= pos && pos < result_vec[j] ==> 
                        !find_substring_at(a[j as usize]@, sub[j as usize]@, pos)) &&

                (sub[j as usize]@.len() == 0 ==> result_vec[j] == start[j as usize]) &&

                (start[j as usize] + sub[j as usize]@.len() > a[j as usize]@.len() ==> result_vec[j] == -1) &&

                (start[j as usize] > end_pos[j as usize] ==> result_vec[j] == -1)
            }
    {
        let cur_start_val = start[i] as int;
        let cur_end_val = end_pos[i] as int;
        let cur_a_len = a[i]@.len() as int;
        let cur_sub_len = sub[i]@.len() as int;

        let mut current_pos: int = cur_start_val;
        let mut found_idx: i32 = -1;

        assert(sub[i]@.len() >= 0) by { substring_length_positive(sub[i]@); }

        if cur_start_val > cur_end_val {
            found_idx = -1;
        } else if cur_sub_len == 0 {
            found_idx = cur_start_val as i32;
        } else if cur_start_val + cur_sub_len > cur_a_len {
            found_idx = -1;
        } else {
            while current_pos <= cur_end_val && current_pos + cur_sub_len <= cur_a_len
                invariant
                    cur_start_val <= current_pos,
                    current_pos <= cur_end_val + 1,
                    (found_idx == -1) == (
                        forall|k: int| cur_start_val <= k < current_pos ==> 
                            !find_substring_at(a[i]@, sub[i]@, k))
            {
                if find_substring_at(a[i]@, sub[i]@, current_pos) {
                    found_idx = current_pos as i32;
                    break;
                }
                current_pos = current_pos + 1;
            }
        }

        assert(
            (found_idx == -1 <==> 
                forall|pos: int| cur_start_val <= pos && pos <= cur_end_val && pos + cur_sub_len <= cur_a_len ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos))) by {
            if found_idx == -1 {
                assert (forall|pos: int| cur_start_val <= pos && pos < current_pos ==> !find_substring_at(a[i]@, sub[i]@, pos));
                if cur_start_val > cur_end_val || cur_sub_len == 0 || cur_start_val + cur_sub_len > cur_a_len {
                    // Handled by outer if conditions, found_idx is pre-set to -1
                } else {
                    assert(current_pos > cur_end_val || current_pos + cur_sub_len > cur_a_len);
                }
                assert(forall|pos: int| cur_start_val <= pos && pos <= cur_end_val && pos + cur_sub_len <= cur_a_len ==> !find_substring_at(a[i]@, sub[i]@, pos));

            } else {
                // found_idx >= 0
                assert(find_substring_at(a[i]@, sub[i]@, found_idx as int));
                assert(forall|pos: int| cur_start_val <= pos && pos < found_idx ==> !find_substring_at(a[i]@, sub[i]@, pos));
            }
        }

        assert(
            (found_idx >= 0 ==> 
                cur_start_val <= found_idx && 
                found_idx <= cur_end_val &&
                found_idx + cur_sub_len <= cur_a_len &&
                find_substring_at(a[i]@, sub[i]@, found_idx as int) &&
                forall|pos: int| cur_start_val <= pos && pos < found_idx ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos))
        ) by {
            if found_idx >= 0 {
                assert(cur_start_val <= found_idx);
                if found_idx as int > cur_end_val {
                    // This case should be covered by the loop condition, or explicit checks.
                    // If it broke out of the loop because of finding `sub`, then `found_idx` would be
                    // `current_pos`, which was `end_pos[i]` or less.
                    // If it found a match, by the loop invariant `current_pos <= end_pos[i]`, 
                    // so `found_idx <= end_pos[i]`
                }
                assert(found_idx as int <= cur_end_val);
                assert(found_idx as int + cur_sub_len <= cur_a_len) by {
                    substring_implies_length_range(a[i]@, sub[i]@, found_idx as int);
                }
            }
        }

        assert(
            (cur_sub_len == 0 ==> found_idx == cur_start_val)) by {
            if cur_sub_len == 0 {
                assert(found_idx == cur_start_val as i32);
            }
        }

        assert(
            (cur_start_val + cur_sub_len > cur_a_len ==> found_idx == -1)) by {
            if cur_start_val + cur_sub_len > cur_a_len {
                assert(found_idx == -1);
            }
        }

        assert(
            (cur_start_val > cur_end_val ==> found_idx == -1)) by {
            if cur_start_val > cur_end_val {
                assert(found_idx == -1);
            }
        }

        result_vec.push(found_idx);
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}