// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): search in a single String using spec-level sequences for correctness */
fn find_seq(hay: String, needle: String, start: i32, end_pos: i32) -> (result: i32)
    requires
        0 <= start,
        start <= end_pos,
        (end_pos as usize) < hay.len(),
    ensures
        (result == -1 <==>
            forall|pos: int| (start as int) <= pos && pos <= (end_pos as int) && pos + needle@.len() <= hay@.len() ==>
                hay@.subrange(pos, pos + needle@.len()) != needle@),
        (result >= 0 ==>
            (start as int) <= (result as int) && (result as int) <= (end_pos as int) && (result as int) + needle@.len() <= hay@.len() &&
            hay@.subrange(result as int, (result as int) + needle@.len()) == needle@ &&
            forall|pos: int| (start as int) <= pos && pos < (result as int) ==>
                hay@.subrange(pos, pos + needle@.len()) != needle@),
{
    let nlen: usize = needle.len();
    let mut pos_usize: usize = start as usize;
    let end_usize: usize = end_pos as usize;
    while pos_usize <= end_usize
        invariant
            (start as usize) <= pos_usize,
            pos_usize <= end_usize + 1,
            forall|q: int| (start as int) <= q && q < (pos_usize as int) ==>
                !(((q as usize) + nlen <= hay.len()) && hay@.subrange(q, q + needle@.len()) == needle@),
        decreases
            (end_usize as int) - (pos_usize as int) + 1
    {
        if pos_usize + nlen <= hay.len() && &hay.as_str()[pos_usize .. pos_usize + nlen] == needle.as_str() {
            return pos_usize as i32;
        }
        pos_usize = pos_usize + 1;
    }
    -1
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
{
    /* code modified by LLM (iteration 5): iterate over items, call find_seq, push results, and maintain invariant with casts */
    let mut result: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            result.len() == j,
            forall|idx: int| 0 <= idx && idx < (j as int) ==>
                (
                    (result[idx as usize] == -1 <==>
                        forall|pos: int| (start[idx as usize] as int) <= pos && pos <= (end_pos[idx as usize] as int) && pos + sub[idx as usize]@.len() <= a[idx as usize]@.len() ==>
                            !find_substring_at(a[idx as usize]@, sub[idx as usize]@, pos)) &&
                    (result[idx as usize] >= 0 ==>
                        (start[idx as usize] as int) <= (result[idx as usize] as int) &&
                        (result[idx as usize] as int) <= (end_pos[idx as usize] as int) &&
                        (result[idx as usize] as int) + sub[idx as usize]@.len() <= a[idx as usize]@.len() &&
                        find_substring_at(a[idx as usize]@, sub[idx as usize]@, result[idx as usize] as int) &&
                        forall|pos: int| (start[idx as usize] as int) <= pos && pos < (result[idx as usize] as int) ==>
                            !find_substring_at(a[idx as usize]@, sub[idx as usize]@, pos)) &&
                    (sub[idx as usize]@.len() == 0 ==> result[idx as usize] == start[idx as usize]) &&
                    ((start[idx as usize] as int) + sub[idx as usize]@.len() > a[idx as usize]@.len() ==> result[idx as usize] == -1) &&
                    (start[idx as usize] > end_pos[idx as usize] ==> result[idx as usize] == -1)
                ),
        decreases
            (a.len() as int) - (j as int)
    {
        let hay_rust: String = a[j].clone();
        let needle_rust: String = sub[j].clone();
        let s: i32 = start[j];
        let e: i32 = end_pos[j];
        let pos: i32 = find_seq(hay_rust, needle_rust, s, e);
        result.push(pos);
        j = j + 1;
    }
    result
}

// </vc-code>

}
fn main() {}