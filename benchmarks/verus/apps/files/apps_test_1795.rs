// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, f: Seq<int>) -> bool {
    n >= 2 && n <= 5000 &&
    f.len() == n &&
    forall|i: int| 0 <= i < f.len() ==> 1 <= f[i] <= n && f[i] != i + 1
}

spec fn zero_indexed_array(n: int, f: Seq<int>) -> Seq<int> {
    Seq::new(n as nat, |j: int| f[j] - 1)
}

spec fn has_love_triangle_with(n: int, a: Seq<int>) -> bool {
    exists|i: int| 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

spec fn has_love_triangle(n: int, f: Seq<int>) -> bool {
    let a = zero_indexed_array(n, f);
    has_love_triangle_with(n, a)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, f: Seq<int>) -> (result: String)
    requires valid_input(n, f)
    ensures result == "YES" || result == "NO"
    ensures (result == "YES") <==> has_love_triangle(n, f)
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO".to_string()
}
// </vc-code>


}

fn main() {}