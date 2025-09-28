use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    let mut res: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i <= n
        invariant res as int == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat)
    {
        if a[i] == v {
            res = res + 1;
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {
}

}