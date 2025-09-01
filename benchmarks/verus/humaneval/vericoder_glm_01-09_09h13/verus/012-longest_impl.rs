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
    let n = strings.len();
    if n == 0 {
        return None;
    }
    let mut current_index = 0;
    let mut current_length = strings[0].len();
    let n_int = n as int;
    for i in 1..n_int
        invariant
            0 <= current_index as int,
            current_index as int < i,
            current_length as int == strings@[current_index].len(),
            forall|j: int| #![trigger strings@[j].len()] 0 <= j < i ==> strings@[j].len() <= current_length as int,
            forall|j: int| #![trigger strings@[j].len()] 0 <= j < current_index as int ==> strings@[j].len() < current_length as int,
    {
        let len_i = strings[i as usize].len();
        if len_i > current_length {
            current_index = i as usize;
            current_length = len_i;
        }
    }
    Some(&strings[current_index])
}
// </vc-code>

fn main() {}
}