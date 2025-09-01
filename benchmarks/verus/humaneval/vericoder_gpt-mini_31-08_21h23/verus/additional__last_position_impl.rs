use vstd::prelude::*;

verus! {

// <vc-helpers>
fn last_pos_rec(a: &[i32], elem: i32, i: usize) -> (result: usize)
    requires
        i < a.len(),
        exists|j: usize| j <= i && a[j] == elem,
    ensures
        result <= i,
        a[result] == elem,
        forall|j: usize| result < j && j <= i ==> a[j] != elem,
    decreases
        i
{
    if i == 0 {
        // i == 0 and exists j <= 0 with a[j] == elem implies a[0] == elem
        proof {
            let j0: usize = choose |j: usize| j <= i && a[j] == elem;
            assert(j0 <= i);
            // since i == 0, j0 == 0
            assert(j0 == 0);
            assert(a[0] == elem);
        }
        0usize
    } else {
        if a[i] == elem {
            i
        } else {
            // from exists j <= i with a[j] == elem and a[i] != elem
            // derive exists j <= i-1 with a[j] == elem
            proof {
                let j0: usize = choose |j: usize| j <= i && a[j] == elem;
                assert(a[j0] == elem);
                assert(!(a[i] == elem));
                // j0 cannot be i, so j0 < i
                assert(j0 != i);
                assert(j0 < i);
                assert(j0 <= i - 1);
                assert(exists|j: usize| j <= i - 1 && a[j] == elem);
            }

            let res = last_pos_rec(a, elem, i - 1);

            // res <= i - 1 implies res <= i, and the other postconditions follow from recursive call
            proof {
                assert(res <= i - 1);
                assert(res <= i);
                assert(a[res] == elem);
                assert(forall|j: usize| res < j && j <= i - 1 ==> a[j] != elem);
                // extend the forall to j <= i by noting a[i] != elem
                assert(forall|j: usize| res < j && j <= i ==> a[j] != elem);
            }

            res
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: usize = a.len();

    // From the function precondition (exists|i: int| 0 <= i < a.len() && a[i] == elem)
    // produce an existence witness in terms of usize for indices <= n-1.
    proof {
        let k: int = choose |k: int| 0 <= k && k < a.len() as int && a[k as usize] == elem;
        assert(0 <= k && k < a.len() as int && a[k as usize] == elem);
        let uk: usize = k as usize;
        assert(uk <= n - 1);
        assert(exists|j: usize| j <= n - 1 && a[j] == elem);
    }

    let result: usize = last_pos_rec(a, elem, n - 1);

    // The helper ensures result <= n-1, a[result] == elem, and no equal elements in (result, n-1].
    // These imply the required postconditions for the original function.
    proof {
        assert(result <= n - 1);
        assert(a[result] == elem);
        assert(forall|j: usize| result < j && j <= n - 1 ==> a[j] != elem);

        // Convert conditions to required types and ranges (using int for quantifiers in the spec)
        assert(0 <= result as int);
        assert(result as int < n as int);
        assert(forall|j: int| result as int < j && j < n as int ==> a[j as usize] != elem);
        assert(a[result as usize] == elem);
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}