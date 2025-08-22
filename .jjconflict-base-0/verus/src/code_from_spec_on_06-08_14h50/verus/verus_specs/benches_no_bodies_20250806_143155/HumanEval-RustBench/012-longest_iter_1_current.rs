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

fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    // post-conditions-start
    ensures
        expr_inner_longest(strings, result),
    // post-conditions-end
{
    if strings.len() == 0 {
        return None;
    }
    
    let mut max_len = 0;
    let mut max_idx = 0;
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < max_len,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
        i += 1;
    }
    
    Some(&strings[max_idx])
}

}
fn main() {}