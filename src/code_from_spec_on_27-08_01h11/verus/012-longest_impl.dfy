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
proof fn lemma_longest_unique(strings: &Vec<Vec<u8>>, max_len: usize, first_idx: usize)
    requires
        0 <= first_idx < strings.len(),
        strings[first_idx as int].len() == max_len,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len,
    ensures
        expr_inner_longest(strings, Some(&strings[first_idx as int])),
{
    let s = &strings[first_idx as int];
    assert(forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len());
    assert(exists|i: int| #![auto] (0 <= i < strings.len() && s == strings[i] && 
        (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < s.len()))) by {
        assert(0 <= first_idx < strings.len() && s == strings[first_idx as int] && 
            (forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < s.len()));
    }
}

proof fn lemma_max_exists(strings: &Vec<Vec<u8>>, max_len: usize)
    requires
        strings.len() > 0,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        exists|i: int| #![auto] 0 <= i < strings.len() && strings[i].len() == max_len,
    ensures
        exists|j: int| #![auto] 0 <= j < strings.len() && strings[j].len() == max_len,
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
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            i > 0 ==> exists|k: int| #![auto] 0 <= k < i && strings[k].len() == max_len,
        decreases strings.len() - i,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
        } else {
            proof {
                if i > 0 {
                    assert(exists|k: int| #![auto] 0 <= k < i && strings[k].len() == max_len);
                }
            }
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < strings.len()
        invariant
            0 <= j <= strings.len(),
            forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() <= max_len,
            exists|k: int| #![auto] 0 <= k < strings.len() && strings[k].len() == max_len,
            forall|k: int| #![auto] 0 <= k < j ==> strings[k].len() < max_len,
        decreases strings.len() - j,
    {
        if strings[j].len() == max_len {
            proof {
                lemma_longest_unique(strings, max_len, j);
            }
            return Some(&strings[j]);
        }
        j += 1;
    }
    
    proof {
        assert(false) by {
            assert(exists|k: int| #![auto] 0 <= k < strings.len() && strings[k].len() == max_len);
            assert(forall|k: int| #![auto] 0 <= k < strings.len() ==> strings[k].len() < max_len);
        }
    }
    unreached()
}
// </vc-code>

}
fn main() {}