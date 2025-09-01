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
proof fn lemma_longest_at_index_satisfies_spec(strings: &Vec<Vec<u8>>, max_idx: usize)
    requires
        strings.len() > 0,
        max_idx < strings.len(),
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[max_idx as int].len() >= strings[i].len(),
        forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len(),
    ensures
        expr_inner_longest(strings, Some(&strings[max_idx]))
{
    let result = &strings[max_idx];
    assert(forall|i: int| #![auto] 0 <= i < strings.len() ==> result.len() >= strings[i].len());
    assert(exists|i: int| #![auto] (0 <= i < strings.len() && result == strings[i] && 
        (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < result.len()))) by {
        assert(0 <= max_idx < strings.len() && result == strings[max_idx as int] && 
            (forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < result.len()));
    };
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
    
    let mut max_len = 0;
    let mut max_idx = 0;
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            strings.len() > 0,
            max_idx < strings.len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[max_idx as int].len() >= strings[j].len(),
            max_len == strings[max_idx as int].len(),
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len(),
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_longest_at_index_satisfies_spec(strings, max_idx);
    }
    
    Some(&strings[max_idx])
}
// </vc-code>

fn main() {}
}