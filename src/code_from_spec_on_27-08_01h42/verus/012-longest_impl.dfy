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
spec fn is_longest_at_position(strings: &Vec<Vec<u8>>, pos: int) -> bool {
    0 <= pos < strings.len() &&
    (forall|i: int| #![auto] 0 <= i < strings.len() ==> strings@[pos].len() >= strings@[i].len()) &&
    (forall|j: int| #![auto] 0 <= j < pos ==> strings@[j].len() < strings@[pos].len())
}

proof fn longest_exists_lemma(strings: &Vec<Vec<u8>>) 
    requires strings.len() > 0
    ensures exists|i: int| is_longest_at_position(strings, i)
{
    let mut max_len: usize = 0;
    let mut max_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant 
            0 <= i <= strings.len(),
            0 <= max_pos < strings.len(),
            max_len == strings[max_pos as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings@[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_pos ==> strings@[j].len() < max_len,
    {
        if strings[i as int].len() > max_len {
            max_len = strings[i as int].len();
            max_pos = i;
        }
        i += 1usize;
    }
    
    assert(is_longest_at_position(strings, max_pos as int));
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
        return None;
    }
    
    let mut max_len: usize = 0;
    let mut max_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant 
            0 <= i <= strings.len(),
            0 <= max_pos < strings.len(),
            max_len == strings[max_pos as int].len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings@[j].len() <= max_len,
            forall|j: int| #![auto] 0 <= j < max_pos ==> strings@[j].len() < max_len,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_pos = i;
        }
        i += 1usize;
    }
    
    Some(&strings[max_pos])
}
// </vc-code>

}
fn main() {}