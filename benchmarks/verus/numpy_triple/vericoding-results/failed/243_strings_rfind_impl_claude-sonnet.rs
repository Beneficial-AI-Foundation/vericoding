// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_starts_with_at(s: Seq<char>, prefix: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + prefix.len() <= s.len() &&
    forall|i: int| 0 <= i < prefix.len() ==> s[pos + i] == prefix[i]
}

/* helper modified by LLM (iteration 5): fixed lemma syntax */
proof fn lemma_string_starts_with_same(s: Seq<char>, prefix: Seq<char>, pos: int)
    ensures string_starts_with(s, prefix, pos) == string_starts_with_at(s, prefix, pos)
{
}

fn find_rightmost_occurrence(s: &String, sub: &String, start_pos: i32, end_pos: i32) -> (result: i32)
    requires
        0 <= start_pos,
        start_pos <= end_pos,
    ensures
        result == -1 || (0 <= result && result < s@.len()),
        result == -1 ==> 
            forall|j: int| start_pos <= j && j + sub@.len() <= end_pos + 1 && 
                           j + sub@.len() <= s@.len() ==> 
                !string_starts_with(s@, sub@, j),
        result >= 0 ==> 
            start_pos <= result && 
            result + sub@.len() <= end_pos + 1 &&
            string_starts_with(s@, sub@, result as int) &&
            (forall|j: int| result < j && j + sub@.len() <= end_pos + 1 && 
                            start_pos <= j && j + sub@.len() <= s@.len() ==> 
                !string_starts_with(s@, sub@, j)),
{
    let mut pos = end_pos;
    let sub_len = sub@.len() as i32;
    
    if sub_len == 0 {
        return pos;
    }
    
    while pos >= start_pos
        invariant
            start_pos <= pos + 1,
            forall|j: int| pos < j && j + sub@.len() <= end_pos + 1 && 
                           start_pos <= j && j + sub@.len() <= s@.len() ==> 
                !string_starts_with(s@, sub@, j),
        decreases pos - start_pos + 1,
    {
        if pos + sub_len <= s@.len() as i32 && pos + sub_len <= end_pos + 1 {
            let mut matches = true;
            let mut i = 0;
            
            while i < sub_len
                invariant
                    0 <= i <= sub_len,
                    matches ==> forall|k: int| 0 <= k < i ==> s@[pos + k] == sub@[k],
            {
                proof {
                    if s@[pos as int + i as int] != sub@[i as int] {
                        matches = false;
                        break;
                    }
                }
                i += 1;
            }
            
            if matches {
                return pos;
            }
        }
        pos -= 1;
    }
    
    -1
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
    /* code modified by LLM (iteration 5): fixed compilation error with ghost types */
    let mut result: Vec<i32> = Vec::with_capacity(a.len());
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (
                (result[j] == -1 || (0 <= result[j] && result[j] < a[j]@.len())) &&
                (result[j] == -1 ==> 
                    forall|k: int| start[j] <= k && k + sub[j]@.len() <= end_pos[j] + 1 && 
                                   k + sub[j]@.len() <= a[j]@.len() ==> 
                        !string_starts_with(a[j]@, sub[j]@, k)) &&
                (result[j] >= 0 ==> 
                    start[j] <= result[j] && 
                    result[j] + sub[j]@.len() <= end_pos[j] + 1 &&
                    string_starts_with(a[j]@, sub[j]@, result[j] as int) &&
                    (forall|k: int| result[j] < k && k + sub[j]@.len() <= end_pos[j] + 1 && 
                                    start[j] <= k && k + sub[j]@.len() <= a[j]@.len() ==> 
                        !string_starts_with(a[j]@, sub[j]@, k)))
            ),
    {
        let found = find_rightmost_occurrence(&a[i], &sub[i], start[i], end_pos[i]);
        result.push(found);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}