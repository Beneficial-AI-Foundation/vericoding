use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        !flag ==> exists|x: int| 0 <= x < a.len() && #[trigger] a[x] != a[a.len() - x - 1],
{
    let mut i: usize = 0;
    while i < a.len() / 2
        invariant
            0 <= i <= a.len() / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] == a[a.len() - j - 1],
    {
        if a[i] != a[a.len() - i - 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}

}