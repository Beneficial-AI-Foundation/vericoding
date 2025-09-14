// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: int, v: Seq<int>) -> bool {
    n > 0 && v.len() == n && s >= 0 && forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
}

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 { 
        0 
    } else { 
        v[0] + sum(v.drop_first()) 
    }
}

spec fn min_seq(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 1 { 
        v[0] 
    } else if v[0] <= min_seq(v.drop_first()) { 
        v[0] 
    } else { 
        min_seq(v.drop_first()) 
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: int, v: Seq<int>) -> (result: int)
    requires 
        valid_input(n, s, v)
    ensures 
        sum(v) < s ==> result == -1,
        sum(v) >= s ==> result == min((sum(v) - s) / n, min_seq(v)),
        result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}