/* For each element, return the lowest index in the string where substring sub is found */

use vstd::prelude::*;

verus! {
spec fn substring_at(s: Seq<char>, start: int, len: nat) -> Seq<char> {
    s.subrange(start, start + len as int)
}
fn find(a: &Vec<String>, sub: &Vec<String>, start: &Vec<int>, end_pos: &Vec<int>) -> (result: Vec<int>)
    requires
        a.len() == sub.len(),
        a.len() == start.len(),
        a.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            0 <= start[i] && start[i] <= end_pos[i] && end_pos[i] < a[i]@.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Case 1: substring not found (returns -1) */
            (result[i] == -1 <==> 
                forall|pos: int| start[i] <= pos && pos <= end_pos[i] && pos + sub[i]@.len() <= a[i]@.len() ==>
                    substring_at(a[i]@, pos, sub[i]@.len()) != sub[i]@) &&
            /* Case 2: substring found (returns non-negative index) */
            (result[i] >= 0 ==> {
                start[i] <= result[i] && 
                result[i] <= end_pos[i] &&
                result[i] + sub[i]@.len() <= a[i]@.len() &&
                /* Substring actually found at this position */
                substring_at(a[i]@, result[i], sub[i]@.len()) == sub[i]@ &&
                /* This is the LOWEST index where substring is found (minimality property) */
                forall|pos: int| start[i] <= pos && pos < result[i] ==>
                    substring_at(a[i]@, pos, sub[i]@.len()) != sub[i]@
            }) &&
            /* Sanity check 1: empty substring is found at start position */
            (sub[i]@.len() == 0 ==> result[i] == start[i]) &&
            /* Sanity check 2: substring longer than remaining string cannot be found */
            (start[i] + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&
            /* Sanity check 3: if start > end, no substring can be found */
            (start[i] > end_pos[i] ==> result[i] == -1)
        },
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}