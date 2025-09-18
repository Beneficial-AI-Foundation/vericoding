// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): minimum of two integers */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
{
    /* code modified by LLM (iteration 5): implement find by scanning each string for sub using nested loops */
    let mut result: Vec<i32> = Vec::new();
    let n: int = a.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant result.len() == i
        decreases n - i
    {
        let hay = a[i]@;
        let needle = sub[i]@;
        let st = start[i] as int;
        let en = end_pos[i] as int;

        if st > en || st + needle.len() > hay.len() {
            result.push(-1);
        } else if needle.len() == 0 {
            result.push(start[i]);
        } else {
            let mut found_pos: int = -1;
            let mut pos: int = st;
            while pos <= en && found_pos == -1
                invariant st <= pos && pos <= en + 1
                invariant found_pos == -1 ==> forall|p: int| st <= p && p < pos ==> !find_substring_at(hay, needle, p)
                decreases en - pos + 1
            {
                if pos + needle.len() <= hay.len() && find_substring_at(hay, needle, pos) {
                    found_pos = pos;
                } else {
                    pos = pos + 1;
                }
            }

            if found_pos == -1 {
                result.push(-1);
            } else {
                result.push(found_pos as i32);
            }
        }

        i = i + 1;
    }

    result
}

// </vc-code>

}
fn main() {}