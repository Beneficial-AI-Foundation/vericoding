use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
// No additional helpers required
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
    while i < v.len()
        invariant
            0 <= i as int <= v@.len(),
            forall|j: int| 0 <= j < i as int ==> v@[j] >= 0
    {
        if v[i] >= 0 {
            proof {
                assert(v@[i as int] >= 0);
            }
            i = i + 1;
        } else {
            proof {
                assert(v@[i as int] < 0);
            }
            break;
        }
    }
    if i == v.len() {
        assert(forall|j: int| 0 <= j < v@.len() ==> v@[j] >= 0);
        return (false, 0);
    } else {
        assert(i as int < v@.len() && v@[i as int] < 0);
        assert(forall|j: int| 0 <= j < i as int ==> v@[j] >= 0);
        return (true, i);
    }
}
// </vc-code>

fn main() {
}

}