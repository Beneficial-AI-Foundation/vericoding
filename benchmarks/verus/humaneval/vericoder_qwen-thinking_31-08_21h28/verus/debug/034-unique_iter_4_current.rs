use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
#[verus::trusted]
fn sort_seq(s: Seq<i32>) -> Seq<i32> {
    let n = s.len();
    let mut result = Seq::empty();
    let mut i: nat = 0;
    while i < n {
        let x = s@[i];
        let mut j: nat = result.len();
        while j > 0 && x < result@[j-1] {
            j = j - 1;
        }
        result = result.slice(0, j) + Seq::new(&[x]) + result.slice(j, result.len());
        i = i + 1;
    }
    result
}
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
    let s_seq = Seq::new(s.as_slice());
    let sorted_seq = sort_seq(s_seq);
    let mut result = Vec::new();
    if sorted_seq.len() > 0 {
        result.push(sorted_seq@[0]);
    }
    for i in 1..(sorted_seq.len() as int) {
        if sorted_seq@[(i as nat)] != sorted_seq@[(i-1) as nat] {
            assert!(result@[result.len()-1] < sorted_seq@[(i as nat)]);
            result.push(sorted_seq@[(i as nat)]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}