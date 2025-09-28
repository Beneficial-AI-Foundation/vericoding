// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define filtered prefix sequence with proofs using assert_forall_by */
open spec fn filter_prefix(cond: Seq<bool>, arr: Seq<i8>, i: int) -> Seq<i8>
    decreases i
{
    if i <= 0 {
        Seq::<i8>::empty()
    } else {
        let r = filter_prefix(cond, arr, i - 1);
        if cond[i - 1] {
            r.push(arr[i - 1])
        } else {
            r
        }
    }
}

/* helper modified by LLM (iteration 5): prove coverage and origin properties of filter_prefix via induction and assert_forall_by */
proof fn lemma_filter_prefix_props(cond: Seq<bool>, arr: Seq<i8>, i: int)
    requires
        0 <= i <= cond.len(),
        i <= arr.len(),
    ensures
        forall|k: int| 0 <= k < filter_prefix(cond, arr, i).len() ==>
            exists|j: int| 0 <= j < i && cond[j] == true && #[trigger] filter_prefix(cond, arr, i)[k] == arr[j],
        forall|j: int| 0 <= j < i && cond[j] == true ==>
            exists|k: int| 0 <= k < filter_prefix(cond, arr, i).len() && #[trigger] filter_prefix(cond, arr, i)[k] == arr[j],
    decreases i
{
    if i == 0 {
        // base case: empty sequence, properties hold vacuously
    } else {
        // inductive step
        lemma_filter_prefix_props(cond, arr, i - 1);
        let r = filter_prefix(cond, arr, i - 1);
        let s = filter_prefix(cond, arr, i);
        let j0 = i - 1;
        if cond[j0] {
            // s == r.push(arr[j0])
            assert(s.len() == r.len() + 1);

            // Each element of s originates from some true position in prefix 0..i
            assert_forall_by(|k: int| {
                requires
                    0 <= k < s.len(),
                ensures
                    exists|j: int| 0 <= j < i && cond[j] == true && #[trigger] s[k] == arr[j],
                proof {
                    if k < r.len() {
                        let j = choose|j: int| 0 <= j < i - 1 && cond[j] == true && #[trigger] r[k] == arr[j];
                        assert(0 <= j && j < i);
                        assert(s[k] == r[k]);
                        assert(exists|j2: int| j2 == j && 0 <= j2 < i && cond[j2] == true && s[k] == arr[j2]);
                    } else {
                        assert(k <= r.len());
                        assert(!(k < r.len()));
                        assert(k == r.len());
                        assert(0 <= j0 && j0 < i);
                        assert(cond[j0] == true);
                        assert(s[k] == arr[j0]);
                        assert(exists|j2: int| j2 == j0 && 0 <= j2 < i && cond[j2] == true && s[k] == arr[j2]);
                    }
                }
            });

            // Every true position j in 0..i contributes an element to s
            assert_forall_by(|j: int| {
                requires
                    0 <= j < i && cond[j] == true,
                ensures
                    exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == arr[j],
                proof {
                    if j == j0 {
                        let k_last = r.len();
                        assert(0 <= k_last && k_last < s.len());
                        assert(s[k_last] == arr[j]);
                        assert(exists|k2: int| k2 == k_last && 0 <= k2 < s.len() && s[k2] == arr[j]);
                    } else {
                        assert(0 <= j && j < i - 1);
                        let k0 = choose|k: int| 0 <= k < r.len() && #[trigger] r[k] == arr[j];
                        assert(0 <= k0 && k0 < r.len());
                        assert(0 <= k0 && k0 < s.len());
                        assert(s[k0] == r[k0]);
                        assert(s[k0] == arr[j]);
                        assert(exists|k2: int| k2 == k0 && 0 <= k2 < s.len() && s[k2] == arr[j]);
                    }
                }
            });
        } else {
            // s == r when cond[j0] is false
            assert(s == r);

            // Each element of s originates from some true position in prefix 0..i
            assert_forall_by(|k: int| {
                requires
                    0 <= k < s.len(),
                ensures
                    exists|j: int| 0 <= j < i && cond[j] == true && #[trigger] s[k] == arr[j],
                proof {
                    let j = choose|j: int| 0 <= j < i - 1 && cond[j] == true && #[trigger] r[k] == arr[j];
                    assert(0 <= j && j < i);
                    assert(s[k] == r[k]);
                    assert(exists|j2: int| j2 == j && 0 <= j2 < i && cond[j2] == true && s[k] == arr[j2]);
                }
            });

            // Every true position j in 0..i contributes an element to s
            assert_forall_by(|j: int| {
                requires
                    0 <= j < i && cond[j] == true,
                ensures
                    exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == arr[j],
                proof {
                    // Since cond[j0] is false, j cannot be j0; hence j < i - 1
                    assert(j <= i - 1);
                    assert(cond[j0] == false);
                    assert(cond[j] == true);
                    // j != j0 follows, therefore j < i - 1
                    assert(j != j0);
                    assert(j < i - 1);
                    let k0 = choose|k: int| 0 <= k < r.len() && #[trigger] r[k] == arr[j];
                    assert(0 <= k0 && k0 < r.len());
                    assert(0 <= k0 && k0 < s.len());
                    assert(s[k0] == r[k0]);
                    assert(s[k0] == arr[j]);
                    assert(exists|k2: int| k2 == k0 && 0 <= k2 < s.len() && s[k2] == arr[j]);
                }
            });
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement filtering with loop invariant tied to spec-level filter_prefix; avoid exec ints and finish with lemma application */
    let n: usize = arr.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i as int <= n as int,
            n == arr.len(),
            n == condition.len(),
            result@ == filter_prefix(condition@, arr@, i as int),
        decreases n - i
    {
        let old_i: usize = i;
        let ghost old_i_int: int = old_i as int; // keep int in ghost context
        let ghost rs = result@;
        proof { assert(rs == filter_prefix(condition@, arr@, old_i_int)); }

        let c_i = condition[i];
        if c_i {
            let v = arr[i];
            result.push(v);
            proof {
                // Using the definition of filter_prefix at index old_i_int + 1
                assert(old_i_int + 1 > 0);
                assert(old_i_int + 1 <= condition@.len());
                assert(old_i_int + 1 <= arr@.len());
                assert(condition@[old_i_int] == c_i);
                assert(result@ == rs.push(arr@[old_i_int]));
                assert(filter_prefix(condition@, arr@, old_i_int + 1) == rs.push(arr@[old_i_int]));
                assert(result@ == filter_prefix(condition@, arr@, old_i_int + 1));
            }
        } else {
            proof {
                assert(old_i_int + 1 > 0);
                assert(old_i_int + 1 <= condition@.len());
                assert(old_i_int + 1 <= arr@.len());
                assert(condition@[old_i_int] == c_i);
                assert(filter_prefix(condition@, arr@, old_i_int + 1) == rs);
                assert(result@ == rs);
                assert(result@ == filter_prefix(condition@, arr@, old_i_int + 1));
            }
        }

        i += 1;
        proof { assert(i as int == old_i_int + 1); }
    }

    proof {
        let i_end: int = n as int;
        assert(arr@.len() == i_end);
        assert(condition@.len() == i_end);
        assert(result@ == filter_prefix(condition@, arr@, i_end));
        lemma_filter_prefix_props(condition@, arr@, i_end);
    }

    result
}
// </vc-code>


}
fn main() {}