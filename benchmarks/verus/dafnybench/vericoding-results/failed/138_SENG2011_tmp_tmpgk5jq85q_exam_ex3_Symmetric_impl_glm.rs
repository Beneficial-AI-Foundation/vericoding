use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i = 0;
    while i < n / 2
        invariant
            forall |j: int| 0 <= j < i ==> a@[j] == a@[n - 1 - j],
            i <= n / 2
        decreases n/2 - i
    {
        if a[i] != a[n - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}

}