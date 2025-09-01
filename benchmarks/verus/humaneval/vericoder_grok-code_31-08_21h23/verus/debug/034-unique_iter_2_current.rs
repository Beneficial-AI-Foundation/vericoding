use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
use vstd::seq_lib::sort;
use vstd::seq_lib::is_sorted;
use vstd::seq_lib;
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let seq_s = s@;
    let sorted = sort(seq_s);
    let mut result = Vec::new();
    let mut prev: Option<i32> = Option::None;
    let mut i = 0;
    while i < sorted.len()
        invariant
            0 <= i <= sorted.len(),
            forall |j: int, k: int| 0 <= j < k < result.len() ==> result[j] < result[k],
            forall |j: int| 0 <= j < result.len() ==> seq_s.contains(result@[j]),
            forall |j: int| 0 <= j < i ==> result@.contains(sorted@[j])
    {
        let x = sorted@[i];
        if prev.is_none() || prev.as_ref().unwrap() < &x {
            result.push(x);
            prev = Some(x);
        }
        i += 1;
    }
    proof {
        assert(is_sorted(result@));
        assert(forall |j: int| 0 <= j < result.len() ==> seq_s.contains(result@[j]));
        assert(forall |j: int| 0 <= j < sorted.len() ==> result@.contains(sorted@[j]));
    }
    result
}
// </vc-code>

fn main() {}
}