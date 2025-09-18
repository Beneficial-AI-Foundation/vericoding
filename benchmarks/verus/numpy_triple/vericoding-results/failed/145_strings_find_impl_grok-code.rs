// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
exec fn substring_matches(haystack: &Vec<char>, needle: &Vec<char>, pos: usize) -> (matches: bool)
{
    if pos + needle.len() > haystack.len() {
        return false;
    }
    let mut j = 0;
    while j < needle.len() {
        if haystack[pos + j] != needle[j] {
            return false;
        }
        j += 1;
    }
    true
}

/* helper modified by LLM (iteration 5): kept existing helper as it's not causing errors */
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
/* code modified by LLM (iteration 5): replaced chars().collect() with manual loop to build Vec<char> to fix compilation error */
{
    let mut result: Vec<i32> = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len() {
        let haystack_str = &a[i];
        let needle_str = &sub[i];
        let mut haystack: Vec<char> = Vec::new();
        for ch in haystack_str.chars() {
            haystack.push(ch);
        }
        let mut needle: Vec<char> = Vec::new();
        for ch in needle_str.chars() {
            needle.push(ch);
        }
        let start_pos = start[i] as usize;
        let end_pos_i = end_pos[i] as usize;
        let needle_len = needle.len();
        let haystack_len = haystack.len();
        let mut found_pos: Option<i32> = None;
        if start_pos > end_pos_i || start_pos + needle_len > haystack_len {
            result.push(-1);
            i += 1;
            continue;
        }
        let mut pos = start_pos;
        while pos <= end_pos_i {
            if substring_matches(&haystack, &needle, pos) {
                found_pos = Some(pos as i32);
                break;
            }
            pos += 1;
        }
        result.push(found_pos.unwrap_or(-1));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}