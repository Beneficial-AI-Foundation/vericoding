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
fn max_len_in_vec(strings: &Vec<Vec<u8>>) -> (max_len: usize)
    ensures
        max_len >= 0,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i as usize].len() <= max_len,
        strings.len() == 0 ==> max_len == 0,
        strings.len() > 0 ==> exists|i: int| #![auto] 0 <= i < strings.len() && strings[i as usize].len() == max_len,
{
    if strings.len() == 0 {
        0
    } else {
        let mut max_len_so_far: usize = 0;
        let mut i: usize = 0;
        
        while i < strings.len()
            invariant
                0 <= i && i <= strings.len(),
                max_len_so_far >= 0,
                forall|j: int| #![auto] 0 <= j < i ==> strings[j as usize].len() <= max_len_so_far,
        {
            let current_len = strings[i].len();
            if current_len > max_len_so_far {
                max_len_so_far = current_len;
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
        let max_len: usize = max_len_in_vec(strings);
        let mut result_idx: isize = -1; // Use isize for index to allow -1 initial value
        let mut i: usize = 0;

        while i < strings.len()
            invariant
                0 <= i && i <= strings.len(),
                max_len >= 0,
                forall|j: int| #![auto] 0 <= j < strings.len() ==> strings[j as usize].len() <= max_len,
                result_idx == -1 || (0 <= result_idx && (result_idx as usize) < strings.len() && strings[result_idx as usize].len() == max_len),
                forall|k: int| #![auto] 0 <= k < i && k as isize != result_idx ==> strings[k as usize].len() < max_len,
            when 
                result_idx == -1
        {
            let current_len = strings[i].len();
            if current_len == max_len {
                // Found the first string with max_len
                result_idx = i as isize;
                break;
            }
            i = i + 1;
        }

        // Proof that result_idx will be valid
        proof {
            assert(result_idx != -1) by {
                // We know strings.len() > 0, so there exists at least one element.
                // max_len_in_vec ensures that `max_len` is the length of at least one string.
                // The loop should find it and assign `result_idx`.
                // This is implicitly covered by the ensures clause of max_len_in_vec:
                // strings.len() > 0 ==> exists|i: int| #![auto] 0 <= i < strings.len() && strings[i as usize].len() == max_len
                // The loop iterates through all elements, so it must eventually find such an `i`.
            }
        }
        assert(result_idx != -1);

        Some(&strings[result_idx as usize])
    }
}
// </vc-code>

fn main() {}
}