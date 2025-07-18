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

//IMPL longest
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    ensures
        expr_inner_longest(strings, result),
{
    /* code modified by LLM (iteration 2): Fixed function signature and implementation */
    if strings.len() == 0 {
        return None;
    }
    
    /* code modified by LLM (iteration 2): Changed max_len to usize type to avoid int usage in executable code */
    let mut max_len: usize = 0;
    let mut max_idx: usize = 0;
    
    /* code modified by LLM (iteration 2): Fixed loop invariants to use consistent types */
    for i in 0..strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < max_len,
    {
        /* code modified by LLM (iteration 2): Removed int casting to fix compilation errors */
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
    }
    
    /* code modified by LLM (iteration 2): Removed int casting for array access */
    Some(&strings[max_idx])
}

}
fn main() {}