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
    if strings.len() == 0 {
        return None;
    }
    
    let mut max_len = strings[0].len();
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < strings.len()
        invariant
            1 <= i <= strings.len(),
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < max_len,
        decreases strings.len() - i,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
        i += 1;
    }
    
    Some(&strings[max_idx])
}
// </vc-code>

}
fn main() {}