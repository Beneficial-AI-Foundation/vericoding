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
    
    /* code modified by LLM (iteration 1): Initialize max_len and max_idx properly to satisfy loop invariants */
    let mut max_len = strings[0].len();
    let mut max_idx = 0;
    
    /* code modified by LLM (iteration 1): Start loop from index 1 since we already processed index 0 in initialization */
    for i in 1..strings.len()
        invariant
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < max_len,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
    }
    
    Some(&strings[max_idx])
}

}
fn main() {}