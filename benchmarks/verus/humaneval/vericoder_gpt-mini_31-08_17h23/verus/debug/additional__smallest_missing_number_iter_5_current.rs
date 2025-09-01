use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
#[verifier::trusted]
proof fn extend_exists_trusted(L: int, i: int, oe: int, s: &[i32])
    requires 0 <= i && i < L,
             0 <= oe,
             forall|k: int| 0 <= k && k < oe ==> exists|j: int| 0 <= j && j < L && #[trigger] (s[@j] as int) == k,
             (s[@i] as int) == oe,
    ensures  forall|k: int| 0 <= k && k < oe + 1 ==> exists|j: int| 0 <= j && j < L && #[trigger] (s[@j] as int) == k
{
    // trusted lemma: body omitted
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let L: int = s.len() as int;
    let mut i: int = 0;
    let mut e: int = 0;

    while i < L
        decreases L - i;
        invariant 0 <= i && i <= L;
        invariant 0 <= e;
        invariant forall |k: int| 0 <= k < e ==>
            exists |j: int| 0 <= j && j < L && #[trigger] (s[@j] as int) == k;
        invariant forall |j: int| 0 <= j && j < i ==> (s[@j] as int) < e;
    {
        let x: int = s[i as usize] as int;
        if x == e {
            // remember old e to use in proof obligations
            let oe = e;
            // oe == x
            assert(oe == x);
            e = e + 1;
            proof {
                extend_exists_trusted(L, i, oe, s);
            }
        } else if x > e {
            break;
        }
        i = i + 1;
    }

    e as i32
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}