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
/* helper modified by LLM (iteration 4): changed to use u32 for executable code */
fn abs_exec(x: i32) -> (abs: u32)
    ensures
        abs as nat == abs_spec(x)
{
    if x >= 0 {
        x as u32
    } else {
        (-x) as u32
    }
}

fn popcount_exec(n: u32) -> (count: u32)
    ensures
        count as nat == popcount(n as nat)
{
    let mut current = n;
    let mut count = 0;
    while current != 0
        invariant
            count + popcount(current as nat) == popcount(n as nat),
        decreases current
    {
        count += current % 2;
        current = current / 2;
    }
    count
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
/* code modified by LLM (iteration 5): fixed type annotation for result_exec vector */
{
    let mut result_exec: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result_exec.len() == i,
            forall|j: int| 0 <= j < i ==> result_exec[j] as nat == popcount(abs_spec(x[j])),
            forall|j: int| 0 <= j < i ==> x[j] == 0 ==> result_exec[j] == 0,
            forall|j: int| 0 <= j < i ==> result_exec[j] >= 0,
        decreases x.len() - i
    {
        let abs_val = abs_exec(x[i]);
        let count = popcount_exec(abs_val);
        result_exec.push(count);
        i += 1;
    }
    
    // Convert executable vector to ghost vector for return
    let ghost result_ghost: Vec<nat> = result_exec@.map(|n| n as nat);
    proof {
        assert(result_ghost.len() == x.len());
        assert(forall|i: int| 0 <= i < result_ghost.len() ==> result_ghost[i] == popcount(abs_spec(x[i])));
        assert(forall|i: int| 0 <= i < result_ghost.len() ==> x[i] == 0 ==> result_ghost[i] == 0);
        assert(forall|i: int| 0 <= i < result_ghost.len() ==> result_ghost[i] >= 0);
    }
    result_ghost
}
// </vc-code>

}
fn main() {}