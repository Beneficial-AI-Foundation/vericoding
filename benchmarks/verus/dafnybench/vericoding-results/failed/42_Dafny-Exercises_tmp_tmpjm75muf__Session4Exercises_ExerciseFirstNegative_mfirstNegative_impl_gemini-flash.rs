use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
#[allow(dead_code)]
fn find_first_negative_in_slice(v: &[int]) -> (found: bool, index: usize) {
    let mut i = 0;
    while i < v.len() {
        if v[i] < 0 {
            return (true, i);
        }
        i += 1;
    }
    (false, 0)
}
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[int]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v.len() && v[k] < 0) &&
        (result.0 ==> (result.1 < v.len() && v[result.1 as int] < 0 && positive(v@.subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let v_len = v.len();

    while i < v_len
        invariant
            0 <= i as int,
            i <= v_len,
            positive(v@.subrange(0, i as int)),
    {
        if v[i as int] < 0 {
            return (true, i);
        }
        i = i + 1;
    }

    proof {
        assert(positive(v@.subrange(0, v_len as int)));
    }

    (false, 0)
}
// </vc-code>

fn main() {
}

}