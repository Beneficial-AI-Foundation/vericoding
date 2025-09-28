// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed insert_sorted invariants and logic */
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn insert_sorted(v: &mut Vec<i32>, pos: usize)
    requires
        0 < pos <= old(v).len(),
        sorted(old(v)@.subrange(0, pos as int)),
    ensures
        sorted(v@.subrange(0, (pos + 1) as int)),
        v@.to_multiset() == old(v)@.to_multiset(),
        v.len() == old(v).len(),
{
    let mut i = pos;
    while i > 0 && v[i - 1] > v[i]
        invariant
            0 <= i <= pos,
            pos <= v.len(),
            v.len() == old(v).len(),
            v@.to_multiset() == old(v)@.to_multiset(),
            sorted(v@.subrange(0, i as int)),
            sorted(v@.subrange(i as int, (pos + 1) as int)),
            forall|j: int, k: int| 0 <= j < i && i < k <= pos ==> v@[j] <= v@[k],
        decreases i
    {
        proof {
            assert(v@.to_multiset() =~= v@.to_multiset());
        }
        let temp = v[i];
        v.set(i, v[i - 1]);
        v.set(i - 1, temp);
        i = i - 1;
        proof {
            assert(v@.to_multiset() == old(v)@.to_multiset());
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop initialization and invariants */
{
    let mut result = l;
    
    if result.len() == 0 {
        return result;
    }
    
    let mut i: usize = 1;
    
    proof {
        assert(sorted(result@.subrange(0, 1))) by {
            assert forall|j: int, k: int| 0 <= j < k < 1 implies result@[j] <= result@[k] by {
                assert(false);
            }
        }
    }
    
    while i < result.len()
        invariant
            1 <= i <= result.len(),
            sorted(result@.subrange(0, i as int)),
            result@.to_multiset() == l@.to_multiset(),
        decreases result.len() - i
    {
        insert_sorted(&mut result, i);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}