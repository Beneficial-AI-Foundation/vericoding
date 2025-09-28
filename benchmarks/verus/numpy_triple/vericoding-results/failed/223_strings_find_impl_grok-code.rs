// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed trailing comma in requires block to fix compilation error */
fn find_one(a: Seq<char>, sub: Seq<char>, start: i32, end_pos: i32) -> (result: i32)
    requires
        0 <= start as int,
        start as int <= end_pos as int,
        end_pos as int < a.len()
    ensures
        result as int == -1 <==>
            forall|pos: int| start as int <= pos && pos <= end_pos as int && pos + sub.len() <= a.len() ==>
                !find_substring_at(a, sub, pos),
        result as int >= 0 ==>
            start as int <= result as int <= end_pos as int &&
            result as int + sub.len() <= a.len() &&
            find_substring_at(a, sub, result as int) &&
            forall|pos: int| start as int <= pos < result as int ==>
                !find_substring_at(a, sub, pos),
        sub.len() == 0 ==> result as int == start as int,
        start as int + sub.len() > a.len() ==> result as int == -1,
        start as int > end_pos as int ==> result as int == -1,
{
    let ghost original_a = a;
    let ghost original_sub = sub;
    let ghost original_start = start as int;
    let ghost original_end_pos = end_pos as int;
    let mut pos = start;
    while (pos as int) + sub.len() <= a.len() && pos <= original_end_pos as i32
        invariant
            start as int <= pos as int <= original_end_pos + 1,
            forall |j: int| start as int <= j < pos as int ==> !find_substring_at(original_a, original_sub, j),
        decreases (original_end_pos - pos as int + 1)
    {
        if find_substring_at(a, sub, pos as int) {
            return pos as i32;
        }
        pos += 1;
    }
    return -1;
}
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
/* code modified by LLM (iteration 5): implemented main logic using fixed helper function */
{
    let mut result = Vec::with_capacity(a.len());
    for i in 0..a.len()
        invariant
            result.len() == i,
    {
        let pos = find_one(a[i]@, sub[i]@, start[i], end_pos[i]);
        result.push(pos);
    }
    result
}
// </vc-code>

}
fn main() {}