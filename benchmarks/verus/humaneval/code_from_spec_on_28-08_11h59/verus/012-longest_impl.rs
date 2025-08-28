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
proof fn lemma_longest_unique(strings: &Vec<Vec<u8>>, i: int, j: int)
    requires
        0 <= i < strings.len(),
        0 <= j < strings.len(),
        i != j,
        (forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= strings[i].len()),
        (forall|k: int| #![auto] 0 <= k < i ==> strings[k].len() < strings[i].len()),
    ensures
        strings[j].len() <= strings[i].len(),
{
    if j < i {
        assert(strings[j].len() < strings[i].len());
    } else {
        assert(strings[j].len() <= strings[i].len());
    }
}

proof fn lemma_max_exists(strings: &Vec<Vec<u8>>, max_len: usize, max_idx: usize)
    requires
        strings.len() > 0,
        max_idx < strings.len(),
        max_len == strings[max_idx as int].len(),
        (forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len),
    ensures
        exists|i: int| #![auto] 0 <= i < strings.len() && strings[i].len() == max_len,
{
    assert(strings[max_idx as int].len() == max_len);
}

proof fn lemma_first_max_property(strings: &Vec<Vec<u8>>, first_max_idx: usize, max_len: usize)
    requires
        strings.len() > 0,
        first_max_idx < strings.len(),
        strings[first_max_idx as int].len() == max_len,
        (forall|k: int| #![auto] 0 <= k < first_max_idx ==> strings[k].len() < max_len),
        (forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= max_len),
    ensures
        exists|i: int| #![auto] 0 <= i < strings.len() && strings[first_max_idx as int] == strings[i] && 
        (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < strings[first_max_idx as int].len()),
{
    let i = first_max_idx as int;
    assert(strings[first_max_idx as int] == strings[i]);
    assert(forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < strings[first_max_idx as int].len());
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
    
    let mut max_len: usize = strings[0].len();
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < strings.len()
        invariant
            0 < strings.len(),
            1 <= i <= strings.len(),
            max_idx < strings.len(),
            max_len == strings[max_idx as int].len(),
            (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len),
        decreases strings.len() - i,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
            max_idx = i;
        }
        i += 1;
    }
    
    let mut first_max_idx: usize = 0;
    let mut j: usize = 0;
    
    while j < strings.len()
        invariant
            0 < strings.len(),
            0 <= j <= strings.len(),
            max_len == strings[max_idx as int].len(),
            (forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= max_len),
            first_max_idx < strings.len(),
            (forall|k: int| #![auto] 0 <= k < j && strings[k].len() < max_len ==> k < first_max_idx),
        invariant_except_break
            if j == 0 {
                first_max_idx == 0
            } else {
                strings[first_max_idx as int].len() == max_len &&
                (forall|k: int| #![auto] 0 <= k < first_max_idx ==> strings[k].len() < max_len)
            },
        decreases strings.len() - j,
    {
        if strings[j].len() == max_len {
            first_max_idx = j;
            break;
        }
        j += 1;
    }
    
    proof {
        lemma_first_max_property(strings, first_max_idx, max_len);
    }
    
    Some(&strings[first_max_idx])
}
// </vc-code>

}
fn main() {}