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
    /* code modified by LLM (iteration 5): Use u32 for result vector in executable code */
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as nat == popcount(abs_spec(x@[j])),
            forall|j: int| 0 <= j < i ==> x@[j] == 0 ==> result@[j] == 0,
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
    {
        let abs_val: u32 = if x[i] >= 0 { x[i] as u32 } else { (-x[i]) as u32 };
        let mut count: u32 = 0;
        let mut n: u32 = abs_val;
        while n > 0
            invariant
                count as nat == popcount(abs_val as nat) - popcount(n as nat),
                count >= 0,
                count <= abs_val,
            decreases n
        {
            count = count + (n % 2);
            n = n / 2;
        }
        assert(n == 0);
        assert(popcount(0) == 0);
        assert(count as nat == popcount(abs_val as nat));
        assert(abs_val as nat == abs_spec(x@[i as int]));
        result.push(count);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}