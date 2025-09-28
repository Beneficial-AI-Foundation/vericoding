use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;
// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let n_usize = a.len();
    let ghost n: int = n_usize as int;
    let a_seq = a@;
    let mut i: usize = 0;
    while i < n_usize / 2
        invariant
            0 <= (i as int) <= n / 2,
            forall |x: int| 0 <= x < (i as int) ==> #[trigger] a_seq[x] == a_seq[n - 1 - x],
    {
        if a[i] != a[n_usize - 1 - i] {
            proof {
                assert(0 <= i as int && i as int < n);
                assert(a@[i as int] == a[i]);
                assert(a@[n - 1 - (i as int)] == a[n_usize - 1 - i]);
                assert(a@[n - 1 - (i as int)] != a@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert forall |x: int| 0 <= x < n ==> #[trigger] a@[x] == a@[n - 1 - x] by {
            if x < (i as int) {
                assert(a@[x] == a@[n - 1 - x]);
            } else {
                let y = n - 1 - x;
                assert(0 <= y < (i as int));
                assert(a@[y] == a@[n - 1 - y]);
                assert(n - 1 - y == x);
                assert(a@[y] == a@[x]);
            }
        }
    }
    return true;
}
// </vc-code>

fn main() {}

}