// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: i32) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn popcount(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable popcount for nat with invariant relating to spec popcount */
fn popcount_nat_exec(n0: nat) -> nat
    ensures result == popcount(n0)
{
    let mut n = n0;
    let mut cnt: nat = 0;
    while n > 0
        invariant n >= 0
        invariant cnt + popcount(n) == popcount(n0)
        decreases n
    {
        if n % 2 == 1 {
            cnt = cnt + 1;
        }
        n = n / 2;
    }
    cnt
}

/* helper modified by LLM (iteration 5): executable popcount for i32 via abs_spec */
fn popcount_i32_exec(x: i32) -> nat
    ensures result == popcount(abs_spec(x))
{
    let n: nat = if x >= 0 { x as nat } else { (-x) as nat };
    popcount_nat_exec(n)
}
// </vc-helpers>

// <vc-spec>
fn bitwise_count(x: Vec<i32>) -> (result: Vec<nat>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
        forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute popcount for each element and return vector */
    let mut res: Vec<nat> = Vec::<nat>::new();
    let mut i: int = 0;
    while i < x.len() {
        invariant 0 <= i && i <= x.len();
        invariant res.len() == i;
        invariant forall|j: int| 0 <= j < res.len() ==> res[j] == popcount(abs_spec(x[j]));
        decreases x.len() - i;
        let v = popcount_i32_exec(x[i]);
        res.push(v);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}