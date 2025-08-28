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
proof fn lemma_longest_unique_first_occurrence(strings: &Vec<Vec<u8>>, max_len: usize, first_idx: usize)
    requires
        first_idx < strings.len(),
        strings[first_idx as int].len() == max_len,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len,
    ensures
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[first_idx as int].len() >= strings[i].len(),
        exists|i: int| #![auto] (0 <= i < strings.len() && strings[first_idx as int] == strings[i] && 
            (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < strings[first_idx as int].len())),
{
    assert(exists|i: int| #![auto] (0 <= i < strings.len() && strings[first_idx as int] == strings[i] && 
        (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < strings[first_idx as int].len())) by {
        assert(strings[first_idx as int] == strings[first_idx as int]);
    })
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
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < strings.len()
        invariant
            0 <= j <= strings.len(),
            forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= max_len,
            forall|k: int| #![auto] 0 <= k < j ==> strings[k].len() < max_len,
    {
        if strings[j].len() == max_len {
            proof {
                lemma_longest_unique_first_occurrence(strings, max_len, j);
            }
            return Some(&strings[j]);
        }
        j += 1;
    }
    
    None
}
// </vc-code>

}
fn main() {}