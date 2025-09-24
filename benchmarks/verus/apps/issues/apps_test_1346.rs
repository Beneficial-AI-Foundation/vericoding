// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, p: int, f: Seq<int>, g: Seq<int>) -> bool {
    n >= 1 && m >= 1 &&
    p >= 2 &&
    f.len() == n && g.len() == m &&
    (forall|k: int| 0 <= k < f.len() ==> f[k] > 0) &&
    (forall|k: int| 0 <= k < g.len() ==> g[k] > 0) &&
    (exists|k: int| 0 <= k < f.len() && f[k] % p != 0) &&
    (exists|k: int| 0 <= k < g.len() && g[k] % p != 0)
}

spec fn valid_result(result: int, n: int, m: int, p: int, f: Seq<int>, g: Seq<int>) -> bool 
    recommends p != 0
{
    exists|i: int, j: int| 0 <= i < f.len() && 0 <= j < g.len() &&
            (forall|k: int| 0 <= k < i ==> f[k] % p == 0) &&
            f[i] % p != 0 &&
            (forall|k: int| 0 <= k < j ==> g[k] % p == 0) &&
            g[j] % p != 0 &&
            result == i + j &&
            0 <= result < f.len() + g.len()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, p: i8, f: Vec<i8>, g: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, p as int, f@.map(|v: i8| v as int), g@.map(|v: i8| v as int)),
        p != 0,
    ensures valid_result(result as int, n as int, m as int, p as int, f@.map(|v: i8| v as int), g@.map(|v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}