use vstd::prelude::*;

verus! {

spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, result: Option<&Vec<u8>>) -> (result: bool) {
    match result {
        None => strings.len() == 0,
        Some(s) => {
            (forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len())
                && (exists|i: int|
                #![auto]
                (0 <= i < strings.len() && s == strings[i] && (forall|j: int|
                    #![auto]
                    0 <= j < i ==> strings[j].len() < s.len())))
        },
    }
}
// pure-end

// <vc-helpers>
fn max_len_in_vec(strings: &Vec<Vec<u8>>) -> (max_len: int)
    requires
        strings.len() >= 0,
    ensures
        max_len >= 0,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        strings.len() == 0 ==> max_len == 0,
        strings.len() > 0 ==> exists|i: int| #![auto] 0 <= i < strings.len() && strings[i].len() == max_len,
{
    if strings.len() == 0 {
        0
    } else {
        let mut max_len_so_far: int = 0;
        let mut i: int = 0;
        while i < strings.len()
            invariant
                0 <= i <= strings.len(),
                max_len_so_far >= 0,
                forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len_so_far,
        {
            if (strings[i].len() as int) > max_len_so_far {
                max_len_so_far = strings[i].len() as int;
            }
            i = i + 1;
        }
        max_len_so_far
    }
}
// </vc-helpers>

// <vc-spec>
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    // post-conditions-start
    ensures
        expr_inner_longest(strings, result),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if strings.len() == 0 {
        None
    } else {
        let max_len: int = max_len_in_vec(strings);
        let mut result_idx: int = -1;
        let mut i: int = 0;

        while i < strings.len()
            invariant
                0 <= i <= strings.len(),
                max_len >= 0,
                forall|j: int| #![auto] 0 <= j < strings.len() ==> strings[j].len() <= max_len,
                result_idx == -1 || (0 <= result_idx < i && strings[result_idx].len() == max_len),
                forall|k: int| #![auto] 0 <= k < i && k != result_idx ==> strings[k].len() < max_len,
        {
             if strings[i].len() as int == max_len {
                result_idx = i;
                break;
            }
            i = i + 1;
        }

        assert(result_idx != -1); // Must find one since strings.len() > 0

        Some(&strings[result_idx as usize])
    }
}
// </vc-code>

fn main() {}
}