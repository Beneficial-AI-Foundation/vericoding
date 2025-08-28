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
proof fn lemma_first_longest_exists(strings: &Vec<Vec<u8>>, max_len: usize)
    requires
        strings.len() > 0,
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        exists|i: int| #![auto] 0 <= i < strings.len() && strings[i].len() == max_len,
    ensures
        exists|first_idx: int| #![auto] 
            0 <= first_idx < strings.len() 
            && strings[first_idx].len() == max_len
            && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len,
{
    let witness_idx = choose|i: int| 0 <= i < strings.len() && strings[i].len() == max_len;
    
    if forall|j: int| #![auto] 0 <= j < witness_idx ==> strings[j].len() < max_len {
        assert(exists|first_idx: int| #![auto] 
            0 <= first_idx < strings.len() 
            && strings[first_idx].len() == max_len
            && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len) by {
            assert(0 <= witness_idx < strings.len());
            assert(strings[witness_idx].len() == max_len);
            assert(forall|j: int| #![auto] 0 <= j < witness_idx ==> strings[j].len() < max_len);
        }
    } else {
        let counter_j = choose|j: int| 0 <= j < witness_idx && strings[j].len() >= max_len;
        assert(strings[counter_j].len() == max_len);
        
        if forall|k: int| #![auto] 0 <= k < counter_j ==> strings[k].len() < max_len {
            assert(exists|first_idx: int| #![auto] 
                0 <= first_idx < strings.len() 
                && strings[first_idx].len() == max_len
                && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len) by {
                assert(0 <= counter_j < strings.len());
                assert(strings[counter_j].len() == max_len);
                assert(forall|k: int| #![auto] 0 <= k < counter_j ==> strings[k].len() < max_len);
            }
        } else {
            lemma_first_longest_exists_recursive(strings, max_len, counter_j);
        }
    }
}

proof fn lemma_first_longest_exists_recursive(strings: &Vec<Vec<u8>>, max_len: usize, upper_bound: int)
    requires
        strings.len() > 0,
        0 <= upper_bound < strings.len(),
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[i].len() <= max_len,
        exists|i: int| #![auto] 0 <= i < strings.len() && strings[i].len() == max_len,
        exists|i: int| #![auto] 0 <= i <= upper_bound && strings[i].len() == max_len,
    ensures
        exists|first_idx: int| #![auto] 
            0 <= first_idx < strings.len() 
            && strings[first_idx].len() == max_len
            && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len,
    decreases upper_bound,
{
    if upper_bound == 0 {
        if strings[0].len() == max_len {
            assert(exists|first_idx: int| #![auto] 
                0 <= first_idx < strings.len() 
                && strings[first_idx].len() == max_len
                && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len) by {
                assert(0 <= 0 < strings.len());
                assert(strings[0].len() == max_len);
                assert(forall|j: int| #![auto] 0 <= j < 0 ==> strings[j].len() < max_len);
            }
        }
    } else {
        if strings[upper_bound].len() == max_len && forall|j: int| #![auto] 0 <= j < upper_bound ==> strings[j].len() < max_len {
            assert(exists|first_idx: int| #![auto] 
                0 <= first_idx < strings.len() 
                && strings[first_idx].len() == max_len
                && forall|j: int| #![auto] 0 <= j < first_idx ==> strings[j].len() < max_len) by {
                assert(0 <= upper_bound < strings.len());
                assert(strings[upper_bound].len() == max_len);
                assert(forall|j: int| #![auto] 0 <= j < upper_bound ==> strings[j].len() < max_len);
            }
        } else {
            assert(exists|i: int| #![auto] 0 <= i < upper_bound && strings[i].len() == max_len);
            lemma_first_longest_exists_recursive(strings, max_len, upper_bound - 1);
        }
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
    
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= max_len,
            i > 0 ==> exists|j: int| #![auto] 0 <= j < i && strings[j].len() == max_len,
        decreases strings.len() - i,
    {
        if strings[i].len() > max_len {
            max_len = strings[i].len();
        }
        i += 1;
    }
    
    proof {
        assert(forall|j: int| #![auto] 0 <= j < strings.len() ==> strings[j].len() <= max_len);
        assert(exists|j: int| #![auto] 0 <= j < strings.len() && strings[j].len() == max_len);
        lemma_first_longest_exists(strings, max_len);
    }
    
    let mut j: usize = 0;
    while j < strings.len()
        invariant
            0 <= j <= strings.len(),
            forall|k: int| #![auto] 0 <= k < j ==> strings[k].len() < max_len,
        decreases strings.len() - j,
    {
        if strings[j].len() == max_len {
            proof {
                assert(forall|k: int| #![auto] 0 <= k < strings.len() ==> max_len >= strings[k].len());
                assert(forall|k: int| #![auto] 0 <= k < j ==> strings[k].len() < max_len);
            }
            return Some(&strings[j]);
        }
        j += 1;
    }
    
    proof {
        assert(false);
    }
    None
}
// </vc-code>

}
fn main() {}