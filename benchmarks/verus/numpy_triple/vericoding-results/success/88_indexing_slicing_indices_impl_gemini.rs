// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn indices(n: u8) -> (grid: Vec<Vec<u8>>)
    ensures 
        grid.len() == 1,
        grid@[0].len() == n as nat,
        forall|i: int| 0 <= i < n as int ==> grid@[0][i] == i as u8,
        forall|i: int, j: int| 0 <= i < j < n as int ==> grid@[0][i] < grid@[0][j],
// </vc-spec>
// <vc-code>
{
    let mut i: u8 = 0;
    let mut v = Vec::new();
    while i < n
        invariant
            i <= n,
            v.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> v@[j] == j as u8,
        decreases n - i
    {
        v.push(i);
        i = i + 1;
    }
    vec![v]
}
// </vc-code>

}
fn main() {}