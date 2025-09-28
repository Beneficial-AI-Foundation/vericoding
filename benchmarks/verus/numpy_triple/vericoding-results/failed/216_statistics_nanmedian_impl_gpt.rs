// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified lemma showing a single finite element refutes all_nan */
proof fn lemma_not_all_nan_from_witness(a: Seq<f32>, i: int)
    requires
        0 <= i,
        i < a.len(),
        a[i] == a[i],
    ensures
        !all_nan(a),
{
    assert(!all_nan(a)) by {
        assert(!(forall|k: int| 0 <= k && k < a.len() ==> a[k] != a[k])) by {
            let k = i;
            assert(0 <= k && k < a.len());
            assert(!(a[k] != a[k]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): linear scan to find a finite element; if none found, return NaN */
    let len: usize = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            forall|j: int| 0 <= j && j < i as int ==> a@[j] != a@[j],
        decreases len as int - i as int
    {
        let v = a[i];
        if v == v {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < a.len() as int);
                assert(a@.len() == a.len() as int);
                assert(0 <= j && j < a@.len());
                assert(a@[j] == v);
                assert(!(a@[j] != a@[j]));
                assert(!all_nan(a@)) by {
                    assert(!(forall|k: int| 0 <= k && k < a@.len() ==> a@[k] != a@[k])) by {
                        let k = j;
                        assert(0 <= k && k < a@.len());
                        assert(!(a@[k] != a@[k]));
                    }
                }
            }
            return v;
        } else {
            proof {
                let j: int = i as int;
                assert(0 <= j && j < a.len() as int);
                assert(a@.len() == a.len() as int);
                assert(0 <= j && j < a@.len());
                assert(a@[j] == v);
                assert(a@[j] != a@[j]);
                assert(forall|k: int| 0 <= k && k < i as int + 1 ==> a@[k] != a@[k]) by {
                    assert forall|k: int| 0 <= k && k < i as int + 1 implies a@[k] != a@[k] by {
                        if k < i as int {
                            assert(0 <= k && k < i as int);
                        } else {
                            assert(k == i as int);
                            assert(a@[k] != a@[k]);
                        }
                    }
                }
            }
            i = i + 1;
        }
    }
    proof {
        assert(i as int == len as int);
        assert(a@.len() == a.len() as int);
        assert(i as int == a@.len());
        assert(forall|j: int| 0 <= j && j < a@.len() ==> a@[j] != a@[j]) by {
            assert forall|j: int| 0 <= j && j < a@.len() implies a@[j] != a@[j] by {
                assert(0 <= j && j < i as int);
            }
        }
        assert(all_nan(a@));
    }
    let nan: f32 = 0.0f32 / 0.0f32;
    assert(nan != nan);
    return nan;
}
// </vc-code>

}
fn main() {}