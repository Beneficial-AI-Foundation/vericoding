// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof lemma_no_occurrence_at_pos(a_str: Seq<char>, sub_str: Seq<char>, pos: int)
    requires
        0 <= pos && pos + sub_str.len() <= a_str.len() && !string_starts_with(a_str, sub_str, pos);
    ensures
        !string_starts_with(a_str, sub_str, pos);
{}

proof lemma_occurrence_found(a_str: Seq<char>, sub_str: Seq<char>, pos: int)
    requires
        0 <= pos && pos + sub_str.len() <= a_str.len() && string_starts_with(a_str, sub_str, pos);
    ensures
        string_starts_with(a_str, sub_str, pos);
{}

fn is_within_search_range(start_i: i32, end_i: i32, pos: i32, sub_len: u32) -> (b: bool)
    ensures
        b == (start_i <= pos && pos + sub_len as i32 <= end_i + 1);
{
    start_i <= pos && pos + sub_len as i32 <= end_i + 1
}

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
    /* code modified by LLM (iteration 5): Fixed compilation error in lemma signature */
    let len = a.len();
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (result[k] == -1 || (0 <= result[k] && result[k] < a[k]@.len())) &&
                (result[k] == -1 ==> 
                    forall|j: int| start[k] <= j && j + sub[k]@.len() <= end_pos[k] + 1 && 
                                   j + sub[k]@.len() <= a[k]@.len() ==> 
                        !string_starts_with(a[k]@, sub[k]@, j)) &&
                (result[k] >= 0 ==> 
                    start[k] <= result[k] && 
                    result[k] + sub[k]@.len() <= end_pos[k] + 1 &&
                    string_starts_with(a[k]@, sub[k]@, result[k] as int) &&
                    forall|j: int| result[k] < j && j + sub[k]@.len() <= end_pos[k] + 1 && 
                                    start[k] <= j && j + sub[k]@.len() <= a[k]@.len() ==> 
                        !string_starts_with(a[k]@, sub[k]@, j))
            )
    {
        let mut found: Option<i32> = None;
        let mut current_pos = end_pos[i];
        let sub_str = sub[i].clone();
        let a_str = a[i].clone();

        while current_pos >= start[i]
            invariant
                current_pos >= start[i] - 1,
                current_pos <= end_pos[i],
                (found.is_some() ==> (
                    let found_pos = found.unwrap();
                    start[i] <= found_pos && found_pos <= end_pos[i] &&
                    found_pos + sub_str@.len() as i32 <= end_pos[i] + 1 &&
                    string_starts_with(a_str@, sub_str@, found_pos as int) &&
                    forall|j: int| found_pos < j && j + sub_str@.len() <= end_pos[i] + 1 && start[i] <= j && j + sub_str@.len() <= a_str@.len() ==> 
                        !string_starts_with(a_str@, sub_str@, j)
                )),
                (found.is_none() ==> (
                    forall|j: int| current_pos < j && j + sub_str@.len() <= end_pos[i] + 1 && start[i] <= j && j + sub_str@.len() <= a_str@.len() ==> 
                        !string_starts_with(a_str@, sub_str@, j)
                ))
        {
            let pos = current_pos;
            if pos >= 0 && pos + sub_str@.len() as i32 <= a_str@.len() as i32 {
                if is_within_search_range(start[i], end_pos[i], pos, sub_str@.len() as u32) {
                    if string_starts_with(a_str@, sub_str@, pos as int) {
                        found = Some(pos);
                        current_pos = start[i] - 1;
                    } else {
                        current_pos = current_pos - 1;
                    }
                } else {
                    current_pos = current_pos - 1;
                }
            } else {
                current_pos = current_pos - 1;
            }
        }

        let final_result = found.unwrap_or(-1);
        result.push(final_result);

        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}