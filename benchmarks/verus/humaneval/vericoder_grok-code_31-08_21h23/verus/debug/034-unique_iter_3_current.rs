use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
use vstd::seq_lib;

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall |i: int| #![auto] 0 <= i < s.len() - 1 ==> s[i] <= s[i + 1]
}

fn swap(s: Seq<i32>, i: int, j: int) -> Seq<i32> {
    s.update(i, s[j]).update(j, s[i])
}

fn my_sort(s: Seq<i32>) -> (result: Seq<i32>) {
    if s.len() <= 1 {
        return s;
    }
    let mut current = s;
    for pass in 0..s.len() - 1
        invariant
            current.len() == s.len()
    {
        for i in 0..s.len() - pass - 1
            invariant
                current.len() == s.len()
        {
            if current[i] > current[i + 1] {
                current = swap(current, i, i + 1);
            }
        }
    }
    current
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
    let seq_s = s@;
    let sorted = my_sort(seq_s);
    let mut result = Vec::new();
    let mut prev: Option<i32> = Option::None;
    let mut i = 0;
    while i < sorted.len()
        invariant
            0 <= i <= sorted.len(),
            forall |j: int, k: int| 0 <= j < k < result.len() ==> result@[j] < result@[k],
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
        assert(is_sorted(sorted));
        assert(forall |x: int, y: int| 0 <= x < y < result.len() ==> result@[x] < result@[y]);
        assert(forall |j: int| 0 <= j < result.len() ==> seq_s.contains(result@[j]));
        assert(forall |j: int| 0 <= j < sorted.len() ==> result@.contains(sorted@[j]));
        assert(forall |p: int| 0 <= p < s.len() ==> result@.contains(s@[p]));
    }
    result
}
// </vc-code>

fn main() {}
}