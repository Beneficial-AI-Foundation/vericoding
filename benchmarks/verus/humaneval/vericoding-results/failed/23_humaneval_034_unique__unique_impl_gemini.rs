// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no logical changes, just updating comment version */
fn find_and_remove_min(v: &mut Vec<i8>) -> (min_val: i8)
    requires
        old(v).len() > 0,
    ensures
        old(v)@.contains(ensures.0),
        forall|x: i8| old(v)@.contains(x) ==> (ensures.0 as int) <= (x as int),
        old(v)@.to_multiset() == v@.to_multiset().insert(ensures.0),
{
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    let v_len = v.len();

    while i < v_len
        invariant
            1 <= i <= v_len,
            0 <= min_idx < v_len,
            *v == *old(v),
            forall|k: int| 0 <= k < i ==> (v@[min_idx] as int) <= (v@[k] as int),
        decreases v_len - i
    {
        if v[i] < v[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    v.remove(min_idx)
}

/* helper modified by LLM (iteration 5): no logical changes, just updating comment version */
fn sort_vec(s: Vec<i8>) -> (res: Vec<i8>)
    ensures
        res@.len() == s@.len(),
        forall|i: int, j: int| 0 <= i < j < res@.len() ==> (res@[i] as int) <= (res@[j] as int),
        res@.to_multiset() == s@.to_multiset(),
{
    let mut temp_s = s;
    let mut result: Vec<i8> = Vec::new();
    let len = temp_s.len();
    while result.len() < len
        invariant
            result@.len() + temp_s@.len() == len,
            result@.to_multiset() + temp_s@.to_multiset() == s@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> (result@[k] as int) <= (result@[l] as int),
            forall|x: i8, y: i8| result@.contains(x) && temp_s@.contains(y) ==> (x as int) <= (y as int),
        decreases temp_s.len()
    {
        let min_val = find_and_remove_min(&mut temp_s);
        result.push(min_val);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error in proof block */
    let sorted_s = sort_vec(s);
    let mut result: Vec<i8> = Vec::new();

    let mut i: usize = 0;
    while i < sorted_s.len()
        invariant
            0 <= i <= sorted_s.len(),
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> (result@[k] as int) < (result@[l] as int),
            forall|x: i8| result@.contains(x) ==> sorted_s@.subrange(0, i as int).contains(x),
            forall|x: i8| sorted_s@.subrange(0, i as int).contains(x) ==> result@.contains(x),
        decreases sorted_s.len() - i
    {
        let current = sorted_s[i];
        if result.len() == 0 || result[result.len() - 1] < current {
            result.push(current);
        }
        i += 1;
    }

    proof {
        vstd::multiset::lemma_multiset_eq_to_set_eq(s@.to_multiset(), sorted_s@.to_multiset());
        vstd::set_lib::assert_sets_equal!(result@.to_set(), sorted_s@.to_set());
        vstd::set_lib::assert_sets_equal!(result@.to_set(), s@.to_set());
    }
    
    result
}
// </vc-code>


}

fn main() {}