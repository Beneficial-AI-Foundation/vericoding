// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error, used get_char_range for UTF-8 correctness */
fn find_one(haystack: &String, needle: &String, start: i32, end_pos: i32) -> (result: i32)
    requires
        0 <= start,
        start <= end_pos,
        end_pos as int < haystack@.len(),
    ensures
        (result == -1 <==>
            forall|pos: int| start as int <= pos && pos <= end_pos as int && pos + needle@.len() <= haystack@.len() ==> 
                !find_substring_at(haystack@, needle@, pos)),
        (result >= 0 ==> 
            start as int <= result as int && 
            result as int <= end_pos as int &&
            result as int + needle@.len() <= haystack@.len() &&
            find_substring_at(haystack@, needle@, result as int) &&
            forall|pos: int| start as int <= pos < result as int ==> 
                !find_substring_at(haystack@, needle@, pos)),
        (needle@.len() == 0 ==> result == start),
        (start as int + needle@.len() > haystack@.len() ==> result == -1)
{
    if needle.is_empty() {
        assert(needle@.len() == 0);
        return start;
    }

    let mut i = start;
    while i <= end_pos
        invariant
            start <= i,
            i <= end_pos + 1,
            forall|pos: int| start as int <= pos < i as int ==>
                !find_substring_at(haystack@, needle@, pos),
        decreases end_pos - i
    {
        if (i as int) + needle@.len() <= haystack@.len() {
            let sub = haystack.get_char_range(i as int, i as int + needle@.len());
            if sub == *needle {
                assert(find_substring_at(haystack@, needle@, i as int));
                return i;
            }
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 5): no changes needed, fix is in helper function */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (result[j] == -1 <==> 
                    forall|pos: int| start[j] as int <= pos && pos <= end_pos[j] as int && pos + sub[j]@.len() <= a[j]@.len() ==>
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (result[j] >= 0 ==> 
                    start[j] as int <= result[j] as int && 
                    result[j] as int <= end_pos[j] as int &&
                    result[j] as int + sub[j]@.len() <= a[j]@.len() &&
                    find_substring_at(a[j]@, sub[j]@, result[j] as int) &&
                    forall|pos: int| start[j] as int <= pos < result[j] as int ==> 
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (sub[j]@.len() == 0 ==> result[j] == start[j]) &&
                (start[j] as int + sub[j]@.len() > a[j]@.len() ==> result[j] == -1) &&
                (start[j] > end_pos[j] ==> result[j] == -1)
            },
            forall|j: int| 0 <= j < a.len() ==> 
                0 <= start[j] && 
                start[j] <= end_pos[j] && 
                (end_pos[j] as int) < a[j]@.len(),
        decreases a.len() - i
    {
        let one_result = find_one(&a[i], &sub[i], start[i], end_pos[i]);
        result.push(one_result);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}