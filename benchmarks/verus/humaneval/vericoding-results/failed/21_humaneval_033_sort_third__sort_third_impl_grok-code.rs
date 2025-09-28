// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by correcting variable name from aSeq to a_seq and removing unused len */
    let mut result = Vec::<i8>::new();
    let a_seq = a@;
    let mut thirds: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < a.len()
    {
        if i % 3 == 0 {
            thirds.push(a[i]);
        }
        i += 1;
    }
    let mut thirds_sorted = thirds.clone();
    let thirds_len = thirds_sorted.len();
    i = 0;
    while i < thirds_len
        invariant
            thirds_sorted@.to_multiset() == thirds@.to_multiset(),
        decreases thirds_len - i
    {
        let mut j = 0;
        while j < thirds_len - i - 1
            invariant
                thirds_sorted@.to_multiset() == thirds@.to_multiset(),
            decreases thirds_len - i - 1 - j
        {
            if thirds_sorted[j] > thirds_sorted[j + 1] {
                thirds_sorted.swap(j, j + 1);
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < thirds_sorted@.len() ==> thirds_sorted@[i] <= thirds_sorted@[j]);
        assert(thirds@.permutation_of(thirds_sorted@));
    }
    let mut idx: usize = 0;
    i = 0;
    while i < a.len()
        invariant
            idx <= thirds_sorted@.len(),
            result@.len() == i as int,
        decreases a.len() - i
    {
        if i % 3 == 0 {
            result.push(thirds_sorted[idx]);
            idx += 1;
        } else {
            result.push(a[i]);
        }
        i += 1;
    }
    proof {
        assert(result@.len() == a@.len());
        assert(forall|i: int, j: int| 0 <= i < j < result@.len() && (i as int) % 3 == 0 && (j as int) % 3 == 0 ==> result@[i] <= result@[j]);
        assert(forall|i: int| 0 <= i < a@.len() && (i as int) % 3 != 0 ==> result@[i] == a@[i]);
        assert(a@.to_multiset() == result@.to_multiset());
    }
    result
}
// </vc-code>


}

fn main() {}