use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
// </vc-spec>
// <vc-code>
{
    let mut j: i32 = 0;
    while j < a.len() as i32
        invariant
            0 <= j as int,
            j as int <= a.len() as int,
            forall|k: int| 0 <= k < j as int ==> #[trigger] a[k] != 0,
        decreases a.len() as int - j as int
    {
        assert(0 <= j as int && j as int < a.len() as int);
        let ui: usize = j as usize;
        assert(ui < a.len());
        if a[ui] == 0 {
            return j;
        }
        let j_old = j;
        proof {
            assert(0 <= j_old as int && j_old as int < a.len() as int);
            assert(a[j_old as int] != 0);
        }
        j += 1;
        proof {
            assert(j as int == j_old as int + 1);
            assert_forall_by(|k: int| {
                requires(0 <= k && k < j as int);
                ensures(a[k] != 0);
                if k < j_old as int {
                    // Holds by the loop invariant from the previous iteration
                } else {
                    assert(k == j_old as int);
                    assert(a[j_old as int] != 0);
                }
            });
        }
    }
    assert(!(j < a.len() as i32));
    assert(j as int <= a.len() as int);
    assert(j as int >= a.len() as int);
    assert(j as int == a.len() as int);
    assert(forall|k: int| 0 <= k < a.len() as int ==> #[trigger] a[k] != 0);
    -1
}
// </vc-code>

fn main() {}

}