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
fn abs_exec(x: i32) -> (res: u32)
    ensures
        res as nat == abs_spec(x),
{
    if x >= 0 {
        x as u32
    } else if x == i32::MIN {
        (1u32 << 31)
    } else {
        (-x) as u32
    }
}

fn popcount_exec(n_u32: u32) -> (count: nat)
    ensures
        count == popcount(n_u32 as nat),
{
    let mut n = n_u32;
    let mut c: nat = 0;
    while n > 0
        invariant
            popcount(n_u32 as nat) == c + popcount(n as nat),
        decreases n
    {
        c = c + (n % 2) as nat;
        n = n / 2;
    }
    c
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == popcount(abs_spec(x[j])),
        decreases x.len() - i
    {
        let abs_val = abs_exec(x[i]);
        let popc = popcount_exec(abs_val);
        result.push(popc);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}