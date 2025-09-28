use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant forall|x: int| 0 <= x && x < (i as int) ==> #[trigger] a[x as usize] == a[a.len() - (x as usize) - 1];
    {
        if a[i] != a[a.len() - i - 1] {
            let w: int = i as int;
            proof {
                assert(0 <= w);
                assert(w < a.len() as int);
                assert(a[w as usize] != a[a.len() - (w as usize) - 1]);
                assert(exists|y: int| a[y as usize] != a[a.len() - (y as usize) - 1] && 0 <= y && y < a.len() as int);
            }
            return (false);
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|x: int| 0 <= x && x < a.len() as int ==> #[trigger] a[x as usize] == a[a.len() - (x as usize) - 1]);
    }
    return (true);
}
// </vc-code>

fn main() {}

}