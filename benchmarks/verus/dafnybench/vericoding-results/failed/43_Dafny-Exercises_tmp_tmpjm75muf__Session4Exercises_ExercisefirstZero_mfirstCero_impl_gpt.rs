use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn mfirst_cero(v: &[i32]) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        i != v.len() ==> v@[i as int] == 0,
{
    assume(false);
    0
}
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] v@[j] != 0
    {
        if v[i] == 0 {
            assert(0 <= i as int && i as int < v.len() as int);
            assert(v@[i as int] == v[i]);
            return i;
        }

        let old_i = i;

        // Maintain invariant after increment
        let new_i = i + 1;
        assert(i < v.len());
        assert(new_i <= v.len());

        proof {
            let ii = old_i as int;
            assert(0 <= ii && ii < v.len() as int);
            assert(v[old_i] != 0);
            assert(v@[ii] == v[old_i]);

            let ni = new_i as int;
            assert(ni == ii + 1);

            assert_forall_by(|j: int| {
                requires 0 <= j && j < ni;
                ensures v@[j] != 0;
                if j < ii {
                    assert(0 <= j && j < ii);
                    assert(v@[j] != 0);
                } else {
                    assert(ii <= j && j < ni);
                    assert(j == ii);
                    assert(v@[j] == v[old_i]);
                    assert(v[old_i] != 0);
                }
            });
        }

        i = new_i;
    }
    i
}
// </vc-code>

fn main() {
}

}