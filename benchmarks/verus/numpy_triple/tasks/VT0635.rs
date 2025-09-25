// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}