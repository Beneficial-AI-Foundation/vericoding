use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn extend_half_to_all(a: &[i32], i: int)
    requires
        0 <= i,
        a.len() <= 2*i + 1,
        forall|k: int| 0 <= k < a.len() && k <= i ==> #[trigger] a[k] == a[a.len() - k - 1],
    ensures
        forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1]
// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    assert(forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1]) by {
        if 0 <= x && x < a.len() {
            if x <= i {
                assert(#[trigger] a[x] == a[a.len() - x - 1]);
            } else {
                assert(x >= i + 1);
                let y = a.len() - x - 1;
                assert(0 <= y);
                assert(y < a.len());
                // y <= i
                assert(y <= a.len() - (i + 1) - 1);
                assert(a.len() - (i + 1) - 1 <= i - 1) by {
                    assert(a.len() <= 2*i + 1);
                }
                assert(y <= i - 1);
                assert(y <= i);
                // apply hypothesis at y
                assert(0 <= y && y < a.len() && y <= i);
                assert(a[y] == a[a.len() - y - 1]);
                assert(a.len() - y - 1 == x);
                assert(a[y] == a[x]);
                assert(a[x] == a[y]);
            }
        }
    };
}
// </vc-code>

fn main() {}

}