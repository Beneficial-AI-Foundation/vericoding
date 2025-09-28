use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
fn idx_is_even(a: &[int], i: int) -> (b: bool)
    requires
        0 <= i < a.len()
    ensures
        b == is_even(a@[i])
{
    let r = a[i as usize] % 2 == 0;
    proof {
        assert(a@[i] == a[i as usize]);
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len()
        invariant forall|j: int| 0 <= j && j < i ==> !is_even(#[trigger] a@[j])
    {
        let b = idx_is_even(a, i);
        if b {
            proof {
                assert(b == is_even(a@[i]));
                assert(is_even(a@[i]));
                assert(0 <= i && i < a.len());
                assert(exists|k: int| 0 <= k && k < a.len() && is_even(#[trigger] a@[k])) by {
                    assert(0 <= i && i < a.len() && is_even(a@[i]));
                }
            }
            return true;
        } else {
            proof {
                assert(b == is_even(a@[i]));
                assert(!is_even(a@[i]));
            }
            let old_i = i;
            i = i + 1;
            proof {
                assert(i == old_i + 1);
                assert(0 <= i);
                assert(old_i < a.len());
                assert(i <= a.len());
                assert(forall|j: int| 0 <= j && j < i ==> !is_even(#[trigger] a@[j])) by {
                    if 0 <= j && j < i {
                        if j < old_i {
                            assert(!is_even(a@[j]));
                        } else {
                            assert(j >= old_i);
                            assert(j < old_i + 1);
                            assert(j <= old_i);
                            assert(j == old_i);
                            assert(!is_even(a@[old_i]));
                            assert(!is_even(a@[j]));
                        }
                    }
                }
            }
        }
    }
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j && j < a.len() ==> !is_even(#[trigger] a@[j]));
        assert(!(exists|k: int| 0 <= k && k < a.len() && is_even(#[trigger] a@[k]))) by {
            if exists|k: int| 0 <= k && k < a.len() && is_even(a@[k]) {
                let k = choose|k: int| 0 <= k && k < a.len() && is_even(a@[k]);
                assert(0 <= k && k < a.len());
                assert(is_even(a@[k]));
                assert(forall|j: int| 0 <= j && j < a.len() ==> !is_even(#[trigger] a@[j]));
                assert(!is_even(a@[k]));
                assert(false);
            }
        }
    }
    false
}
// </vc-code>

fn main() {
}

}