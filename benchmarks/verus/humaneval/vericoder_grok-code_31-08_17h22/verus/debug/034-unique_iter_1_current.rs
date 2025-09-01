use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
// No updates needed for helpers in this implementation
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
        assert(seq_lib::seq_is_sorted(result@));
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j]);
    }
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            seq_lib::seq_is_sorted(result@),
            forall|a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
            forall|k: int| 0 <= k < i ==> result@.contains(s[k]),
            forall|v: i32| result@.contains(v) ==> exists|k: int| 0 <= k < i && s[k] == v
    {
        let val = s[i];
        proof {
            assert(forall|a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b]);
        }
        let mut j: nat = 0;
        let mut present = false;
        while j < result.len()
            invariant
                j <= result.len(),
                present == exists|k: nat| 0 <= k < j && result[k] == val
        {
            if result[j] == val {
                present = true;
                break;
            }
            j = j + 1;
        }
        if !present {
            let mut k: nat = 0;
            while k < result.len()
                invariant
                    k <= result.len(),
                    forall|l: int| 0 <= l < k ==> val >= result[l]
            {
                if val < result[k] {
                    result.insert(k, val);
                    proof {
                        assert(seq_lib::seq_is_sorted(result@));
                        assert(forall|a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b]);
                    }
                    break;
                }
                k = k + 1;
            }
            if k == result.len() {
                result.push(val);
                proof {
                    assert(seq_lib::seq_is_sorted(result@));
                    assert(forall|a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b]);
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