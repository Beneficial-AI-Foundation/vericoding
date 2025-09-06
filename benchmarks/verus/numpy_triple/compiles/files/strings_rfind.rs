/* For each element, return the highest index in the string where substring sub is found, such that sub is contained within [start, end]

For each element, return the highest index in the string where substring is found

Specification: rfind returns the highest index where substring is found within range, or -1 if not found */

use vstd::prelude::*;

verus! {
fn rfind(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < start.len() ==> 0 <= start[i] && start[i] <= end_pos[i],
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Basic range constraint */
            (result[i] == -1 || (0 <= result[i] && result[i] < a[i].view().len())) &&
            /* If non-negative, matches at position and is within search range */
            (result[i] >= 0 ==> {
                start[i] <= result[i] && 
                result[i] + sub[i].view().len() <= end_pos[i] + 1 &&
                a[i].view().subrange(result[i] as int, result[i] as int + sub[i].view().len()) =~= sub[i].view()
            })
        },
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}