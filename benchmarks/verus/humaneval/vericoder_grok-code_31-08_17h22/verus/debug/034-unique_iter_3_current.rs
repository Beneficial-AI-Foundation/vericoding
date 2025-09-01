use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
spec fn seq_is_sorted(s: Seq<i32>) -> bool {
    forall |i: int, j: int| #![auto] 0 <= i < j < s.len() ==> s[i] < s[j]
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
    let mut result = Vec::<i32>::new();
    proof {
        assert(seq_is_sorted(result@));
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            seq_is_sorted(result@),
            forall |k: int| #![auto] 0 <= k < i ==> result@.contains(s[k]),
            forall |v: i32| #![auto] result@.contains(v) ==> exists |k: int| #![trigger s[k]] 0 <= k < i && s[k] == v
    {
        let val = s[i];
        let mut j: usize = 0;
        let mut present = false;
        while j < result.len()
            invariant
                j <= result.len(),
                present == exists |k: int| #![trigger result[k]] 0 <= k < j && result[k] == val
        {
            if result[j] == val {
                present = true;
                break;
            }
            j = j + 1;
        }
        if !present {
            let mut k: usize = 0;
            while k < result.len()
                invariant
                    k <= result.len(),
                    forall |l: int| #![auto] 0 <= l < k ==> val >= result[l]
            {
                if val < result[k] {
                    result.insert(k, val);
                    proof {
                        assert(seq_is_sorted(result@));
                    }
                    break;
                }
                k = k + 1;
            }
            if k == result.len() {
                result.push(val);
                proof {
                    assert(seq_is_sorted(result@));
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}