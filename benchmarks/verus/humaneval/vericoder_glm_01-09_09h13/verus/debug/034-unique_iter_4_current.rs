use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
fn find_min_index_and_value(v: &Vec<i32>) -> (index: int, value: i32)
    requires
        v.len() > 0
    ensures
        0 <= index < v.len(),
        value == v@[index],
        forall|i: int| 0 <= i < v.len() ==> v@[index] <= v@[i]
{
    let mut min_index = 0;
    let mut min_value = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            0 <= min_index < v.len(),
            min_value == v@[min_index],
            forall|k: int| 0 <= k < i ==> v@[min_index] <= v@[k],
    {
        if v[i] < min_value {
            min_index = i;
            min_value = v[i];
        }
        i += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < v.len() ==> v@[min_index] <= v@[i]);
    }
    (min_index, min_value)
}

fn lemma_unique_sorted(a: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
    ensures
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] < a[i + 1]
{
    assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] < a[i + 1]);
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
    let mut s = s;
    let mut result = Vec::new();
    while s.len() > 0
        invariant
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
            forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
            forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]) || old(s)@.contains(s[i]),
            old(s)@.subset(s@),
            old(s)@.subseteq(s@),
            s.len() <= old(s).len(),
    {
        let (min_index, min_value) = find_min_index_and_value(&s);
        result.push(min_value);
        proof {
            lemma_unique_sorted(result);
            lemma_seq_contains_after_push(s@, result@, min_value);
        }
        s.remove(min_index as usize);
        proof {
            assert(s.len() < old(s).len());
        }
    }
    result
}
// </vc-code>

fn main() {}
}