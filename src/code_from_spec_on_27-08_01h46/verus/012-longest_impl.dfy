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
spec fn is_longest_at_index(strings: &Vec<Vec<u8>>, idx: int) -> bool {
    0 <= idx < strings.len() &&
    (forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[idx].len() >= strings[i].len()) &&
    (forall|j: int| #![auto] 0 <= j < idx ==> strings[j].len() < strings[idx].len())
}

proof fn lemma_longest_exists(strings: &Vec<Vec<u8>>)
    requires strings.len() > 0
    ensures exists|i: int| is_longest_at_index(strings, i)
{
    let mut max_len: int = 0;
    let mut max_idx: usize = 0;
    
    for i in 0..strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx].len() as int,
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() as int <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() as int < max_len,
    {
        if strings[i].len() as int > max_len {
            max_len = strings[i].len() as int;
            max_idx = i;
        }
    }
    
    proof {
        assert(is_longest_at_index(strings, max_idx as int));
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
        return None;
    }
    
    let mut max_len: int = 0;
    let mut max_idx: usize = 0;
    
    for i in 0..strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx].len() as int,
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() as int <= max_len,
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() as int < max_len,
    {
        if strings[i].len() as int > max_len {
            max_len = strings[i].len() as int;
            max_idx = i;
        }
    }
    
    proof {
        assert(forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < strings[max_idx].len());
        assert(forall|j: int| #![auto] 0 <= j < strings.len() ==> strings[j].len() <= strings[max_idx].len());
    }
    
    Some(&strings[max_idx])
}
// </vc-code>

}
fn main() {}