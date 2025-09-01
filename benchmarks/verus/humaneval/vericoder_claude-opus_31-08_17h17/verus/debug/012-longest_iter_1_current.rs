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
// No additional helpers needed
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
    
    let mut max_idx: usize = 0;
    let mut max_len: usize = strings[0].len();
    
    let mut i: usize = 1;
    while i < strings.len()
        invariant
            0 <= max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            0 <= i <= strings.len(),
            forall|j: int| 0 <= j < i ==> strings[max_idx as int].len() >= strings[j].len(),
            forall|j: int| 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len(),
    {
        if strings[i].len() > max_len {
            max_idx = i;
            max_len = strings[i].len();
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < strings.len() ==> strings[max_idx as int].len() >= strings[j].len());
    assert(forall|j: int| 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len());
    
    Some(&strings[max_idx])
}
// </vc-code>

fn main() {}
}