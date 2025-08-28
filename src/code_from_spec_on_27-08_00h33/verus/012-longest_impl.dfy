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
proof fn lemma_longest_unique(strings: &Vec<Vec<u8>>, idx: usize)
    requires
        idx < strings.len(),
        forall|j: int| 0 <= j < idx ==> strings@[j].len() < strings@[idx as int].len(),
        forall|i: int| 0 <= i < strings.len() ==> strings@[idx as int].len() >= strings@[i].len()
    ensures
        expr_inner_longest(strings, Some(&strings[idx as int]))
{
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
    
    let mut max_len = strings[0].len();
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < strings.len()
        invariant
            0 < i <= strings.len(),
            max_idx < strings.len(),
            max_len == strings@[max_idx as int].len(),
            forall|j: int| 0 <= j < i ==> strings@[j].len() <= max_len,
            forall|j: int| 0 <= j < max_idx ==> strings@[j].len() < max_len
        decreases strings.len() - i
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_longest_unique(strings, max_idx);
    }
    
    Some(&strings[max_idx])
}
// </vc-code>

}
fn main() {}