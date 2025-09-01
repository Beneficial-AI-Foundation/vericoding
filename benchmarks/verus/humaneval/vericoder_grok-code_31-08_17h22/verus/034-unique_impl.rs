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
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            seq_is_sorted(result@),
            forall |k: int| #![auto] 0 <= k < i ==> result@.contains(s[k]),
            forall |v: i32| #![auto] result@.contains(v) ==> exists |k: int| #![trigger s[k]] 0 <= k < i && s[k] == v
        decreases s.len() - i
    {
        let val = s[i];
        let mut j: usize = 0;
        let mut present = false;
        while j < result.len()
            invariant
                j <= result.len(),
                present == exists |k: int| #![trigger result[k]] 0 <= k < result.len() && result[k] == val
            decreases result.len() - j
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
                decreases result.len() - k
            {
                if val < result[k] {
                    result.insert(k, val);
                    proof {
                        let new_result = result@;
                        let len_new = new_result.len();
                        let k_int = k as int;
                        assert(forall |i: int, j_t: int| #![auto] 0 <= i < j_t < k_int ==> new_result[i] < new_result[j_t]);
                        assert(forall |i: int, j_t: int| #![auto] k_int < i < j_t < len_new ==> new_result[i] < new_result[j_t]); // Because it's the same as old@[k..] and j=i+1, so i+1 corresponds to k+1, etc.
                        assert(forall |i: int| k_int <= i < len_new - 1 ==> new_result[i] < new_result[i + 1]);
                        if k_int > 0 {
                            assert(forall |i: int| 0 <= i < k_int && k_int < i + 1 < len_new ==> new_result[i] <= val && val < new_result[k_int + 1]);
                        }
                        if k_int == 0 {
                            assert(forall |i: int| 0 <= i < len_new - 1 ==> new_result[i] < new_result[i + 1]);
                        }
                    }
                    break;
                }
                k = k + 1;
            }
            if k == result.len() {
                result.push(val);
                proof {
                    let new_result = result@;
                    let len_new = new_result.len();
                    let k_int = k as int;
                    assert(forall |i: int, j_t: int| #![auto] 0 <= i < j_t < len_new ==> new_result[i] < new_result[j_t]);
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