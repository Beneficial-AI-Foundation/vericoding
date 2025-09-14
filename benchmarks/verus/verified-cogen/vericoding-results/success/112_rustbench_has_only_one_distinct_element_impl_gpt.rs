// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add trigger to quantifier to guide SMT */
spec fn up_to_all_eq(a: &[i32], n: int) -> bool
    recommends 0 <= n && n <= a.len() as int && a.len() as int > 0
{
    forall|k: int| 0 <= k && k < n ==> #[trigger] a[k] == a[0]
}

/* helper modified by LLM (iteration 2): construct explicit witnesses for inequality */
proof fn witnesses_exist_for_neq(a: &[i32], i: int, j: int)
    requires
        0 <= i < a.len() as int,
        0 <= j < a.len() as int,
        a[i] != a[j]
    ensures
        exists|ii: int, jj: int| 0 <= ii < a.len() as int && 0 <= jj < a.len() as int && a[ii] != a[jj]
{
    let ii = i;
    let jj = j;
    assert(0 <= ii && ii < a.len() as int);
    assert(0 <= jj && jj < a.len() as int);
    assert(a[ii] != a[jj]);
    assert(exists|ii2: int, jj2: int| 0 <= ii2 && ii2 < a.len() as int && 0 <= jj2 && jj2 < a.len() as int && a[ii2] != a[jj2]) by {
        let ii2 = ii;
        let jj2 = jj;
        assert(0 <= ii2 && ii2 < a.len() as int);
        assert(0 <= jj2 && jj2 < a.len() as int);
        assert(a[ii2] != a[jj2]);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added trigger annotations and used witness lemma to satisfy existential; kept loop invariant */
    if a.len() == 0 {
        return true;
    }
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i && i <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> #[trigger] a[k] == a[0]
        decreases a.len() - i
    {
        if a[i] != a[0] {
            proof {
                let i_int: int = i as int;
                assert(0 <= i_int && i_int < a.len() as int);
                assert(0 <= 0 && 0 < a.len() as int);
                assert(a[i_int] != a[0]);
                witnesses_exist_for_neq(a, i_int, 0);
            }
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}