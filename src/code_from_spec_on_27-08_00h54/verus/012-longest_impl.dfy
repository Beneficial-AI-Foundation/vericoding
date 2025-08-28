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
proof fn lemma_longest_element_exists(strings: &Vec<Vec<u8>>, max_len: usize, first_max_idx: usize)
    requires
        strings.len() > 0,
        0 <= first_max_idx < strings.len(),
        strings[first_max_idx as int].len() == max_len,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        forall|j: int| #![auto] 0 <= j < first_max_idx ==> strings[j].len() < max_len,
    ensures
        expr_inner_longest(strings, Some(&strings[first_max_idx as int])),
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
    
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
        decreases strings.len() - i
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
        }
        i += 1;
    }
    
    let mut first_max_idx: usize = 0;
    let mut j: usize = 0;
    
    while j < strings.len()
        invariant
            0 <= j <= strings.len(),
            0 <= first_max_idx < strings.len(),
            forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= max_len,
            forall|k: int| #![auto] 0 <= k < j ==> strings[k].len() < max_len,
            j > 0 ==> strings[first_max_idx as int].len() == max_len,
        decreases strings.len() - j
    {
        if strings[j as int].len() == max_len {
            first_max_idx = j;
            break;
        }
        j += 1;
    }
    
    proof {
        assert(j <= strings.len());
        if j == strings.len() {
            assert(forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() < max_len);
            assert(false);
        }
        assert(strings[j as int].len() == max_len);
        assert(strings[first_max_idx as int].len() == max_len);
        lemma_longest_element_exists(strings, max_len, first_max_idx);
    }
    
    Some(&strings[first_max_idx])
}
// </vc-code>

}
fn main() {}