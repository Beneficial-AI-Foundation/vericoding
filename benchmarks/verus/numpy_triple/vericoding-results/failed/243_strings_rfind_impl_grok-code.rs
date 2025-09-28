// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Converted Vec indexing in ensures to use @ for Seq access to match spec types */
fn is_prefix(s: &Vec<char>, prefix: &Vec<char>, pos: i32) -> (b: bool)
    requires
        0 <= pos,
        (pos + prefix.len() as i32) <= s.len() as i32,
    ensures
        b <==> forall|i: int| 0 <= i < prefix@.len() ==> s@[pos as int + i] == prefix@[i]
{
    let mut i = 0;
    while i < prefix.len() as i32
        invariant
            0 <= i <= prefix.len() as i32,
            forall|k: int| 0 <= k < i as int ==> s[(pos + k as i32) as usize] == prefix[k as usize],
        decreases prefix.len() - i as int
    {
        if s[(pos + i) as usize] != prefix[i as usize] {
            return false;
        }
        i += 1;
    }
    return true;
}

/* helper modified by LLM (iteration 5): Fixed typo 'is usize' to 'as usize', converted Vec indexing in ensures to use @ for Seq access */
fn rfind_one(s: &Vec<char>, sub: &Vec<char>, start_pos: i32, end_excl: i32) -> (result: i32)
    requires
        0 <= start_pos <= end_excl <= s.len() as i32,
    ensures
        (result == -1 || (start_pos <= result && result + (sub.len() as i32) <= end_excl &&
            forall|i: int| 0 <= i < sub@.len() ==> s@[result as int + i] == sub@[i])) &&
        (result == -1 ==> forall|j: int| start_pos <= j && j + (sub.len() as i32) <= end_excl ==>
            exists|i: int| 0 <= i < sub@.len() && s@[j as int + i] != sub@[i]) &&
        (result >= 0 ==> forall|j: int| start_pos <= j < result && j + (sub.len() as i32) <= end_excl ==>
            exists|i: int| 0 <= i < sub@.len() && s@[j as int + i] != sub@[i])
{
    let sub_len = sub.len() as i32;
    if sub_len == 0 {
        return end_excl - 1;
    }
    let end_max = end_excl - sub_len;
    if end_max < start_pos {
        return -1;
    }
    let mut j = end_max;
    while j >= start_pos
        invariant
            start_pos <= j <= end_max,
            forall|k: int| end_max >= k > j && start_pos <= k && k + (sub.len() as i32) <= end_excl ==>
                exists|p: int| 0 <= p < sub@.len() && s@[k as int + p] != sub@[p],
        decreases j - start_pos
    {
        if is_prefix(s, sub, j) {
            return j;
        }
        j -= 1;
    }
    return -1;
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
/* code modified by LLM (iteration 5): Implemented exec version using &Vec<char> for rfind_one, removed casts and proof block */
{
    let mut result = Vec::<i32>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
        decreases a.len() - i
    {
        let start_p: i32 = start[i];
        let end_e: i32 = end_pos[i] + 1;
        let s_vec: Vec<char> = a[i].chars().collect::<Vec<_>>();
        let sub_vec: Vec<char> = sub[i].chars().collect::<Vec<_>>();
        let res = rfind_one(&s_vec, &sub_vec, start_p, end_e);
        result.push(res);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}