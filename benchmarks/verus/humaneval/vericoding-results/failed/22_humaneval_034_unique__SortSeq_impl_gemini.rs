// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn insert_sorted(s_sorted: Vec<i8>, x: i8) -> (res: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < s_sorted@.len() ==> s_sorted@[i] <= s_sorted@[j],
    ensures
        res@.len() == s_sorted@.len() + 1,
        res@.to_multiset() == s_sorted@.to_multiset().add(x),
        forall|i: int, j: int| 0 <= i < j < res@.len() ==> res@[i] <= res@[j],
    decreases s_sorted.len()
{
    if s_sorted.len() == 0 {
        let mut v = Vec::new();
        v.push(x);
        return v;
    }

    let s_spec = s_sorted@;
    let mut prefix_vec = s_sorted;
    let last = prefix_vec.pop().unwrap();

    if x >= last {
        prefix_vec.push(last);
        prefix_vec.push(x);
        proof {
            let original_s_spec = prefix_vec@.subrange(0, prefix_vec@.len() - 1);
            assert_seqs_equal!(original_s_spec, s_spec);
            
            forall|k: int| 0 <= k < original_s_spec.len() implies original_s_spec[k] <= last by {
                assert(original_s_spec[k] <= original_s_spec[original_s_spec.len()-1]);
            }
            vstd::seq_lib::lemma_push_sorted(original_s_spec, x);
        }
        return prefix_vec;
    } else {
        let rec_res = insert_sorted(prefix_vec, x);
        let mut res = rec_res;
        res.push(last);
        proof {
            let prefix_spec = prefix_vec@;
            let rec_res_spec = res@.subrange(0, res@.len() - 1);
            
            assert(forall|i: int, j: int| 0 <= i < j < rec_res_spec.len() ==> rec_res_spec[i] <= rec_res_spec[j]);
            assert(rec_res_spec.to_multiset() === prefix_spec.to_multiset().add(x));
            
            forall|elt: i8| rec_res_spec.to_multiset().count(elt) > 0 implies elt <= last by {
                if elt == x {
                    assert(x < last);
                } else {
                    assert(prefix_spec.to_multiset().count(elt) > 0);
                    let idx = prefix_spec.index_of(elt).unwrap();
                    let full_s_spec = prefix_spec.push(last);
                    assert_seqs_equal!(full_s_spec, s_spec);
                    assert(full_s_spec[idx] <= full_s_spec[full_s_spec.len()-1]);
                    assert(elt <= last);
                }
            }
            vstd::seq_lib::lemma_push_sorted(rec_res_spec, last);
        }
        return res;
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut sorted_vec = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int, k: int| 0 <= j < k < sorted_vec@.len() ==> sorted_vec@[j] <= sorted_vec@[k],
            sorted_vec@.len() == i,
            sorted_vec@.to_multiset() == s@.subrange(0, i as int).to_multiset(),
    {
        let element = s[i];
        sorted_vec = insert_sorted(sorted_vec, element);
        i = i + 1;
    }
    proof {
        assert_seqs_equal!(s@.subrange(0, s@.len() as int), s@);
    }
    sorted_vec
}
// </vc-code>


}

fn main() {}