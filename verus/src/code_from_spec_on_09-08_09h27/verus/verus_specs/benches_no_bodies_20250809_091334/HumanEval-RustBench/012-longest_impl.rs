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
    
    /* code modified by LLM (iteration 1): Fixed type conversions and loop invariants */
    let mut max_len = strings[0].len();
    let mut max_index: usize = 0;
    
    for i in 0..strings.len()
        invariant
            0 <= max_index < strings.len(),
            max_len == strings[max_index as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_index ==> strings[j].len() < max_len,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_index = i;
        }
    }
    
    Some(&strings[max_index])
}

}
fn main() {}