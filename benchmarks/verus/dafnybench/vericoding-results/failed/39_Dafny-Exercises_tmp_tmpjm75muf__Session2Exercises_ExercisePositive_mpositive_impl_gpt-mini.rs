use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
proof fn slice_seq_len(v: &[int]) {
    // The sequence view of a slice has the same length as the slice's length
    assert(v@.len() == (v.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let mut i: usize = 0;
    let mut ok: bool = true;
    while (i < n)
        invariant i <= n;
        invariant ok == (forall|j: int| 0 <= j && j < (i as int) ==> v@[j] >= 0);
        decreases n - i;
    {
        if v[i] < 0 {
            ok = false;
        }
        i = i + 1;
    }
    proof {
        assert(i == n);
        slice_seq_len(v);
        assert(ok == (forall|j: int| 0 <= j && j < (n as int) ==> v@[j] >= 0));
        assert((forall|j: int| 0 <= j && j < (n as int) ==> v@[j] >= 0) == positive(v@));
    }
    ok
}
// </vc-code>

fn main() {
}

}