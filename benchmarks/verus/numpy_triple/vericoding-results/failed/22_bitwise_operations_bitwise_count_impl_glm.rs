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
/* helper modified by LLM (iteration 5): added executable abs function and proof */
fn abs_exec(x: i32) -> nat {
    if x >= 0 {
        x as nat
    } else {
        (-x) as nat
    }
}

proof fn abs_exec_equiv(x: i32)
    ensures
        abs_exec(x) == abs_spec(x)
{
    if x >= 0 {
        assert(abs_exec(x) == x as nat);
        assert(abs_spec(x) == x as nat);
    } else {
        assert(abs_exec(x) == (-x) as nat);
        assert(abs_spec(x) == (-x) as nat);
    }
}

/* helper modified by LLM (iteration 5): added executable popcount function and proof */
fn popcount_exec(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount_exec(n / 2)
    }
}

proof fn popcount_exec_equiv(n: nat)
    ensures
        popcount_exec(n) == popcount(n)
    decreases n
{
    if n == 0 {
        assert(popcount_exec(0) == 0);
        assert(popcount(0) == 0);
    } else {
        popcount_exec_equiv(n / 2);
        assert(popcount_exec(n) == (n % 2) + popcount_exec(n / 2));
        assert(popcount(n) == (n % 2) + popcount(n / 2));
    }
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
    /* code modified by LLM (iteration 5): replaced spec function calls with executable versions and added proofs */
    let len = x.len();
    let mut result: Vec<nat> = Vec::new();
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == popcount(abs_spec(x[j])),
            forall|j: int| 0 <= j < i ==> x[j] == 0 ==> result[j] == 0,
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
    {
        let xi = x[i];
        let abs_val = abs_exec(xi);
        let count = popcount_exec(abs_val);

        proof {
            // Prove that the computed count equals the spec value
            abs_exec_equiv(xi);
            popcount_exec_equiv(abs_val);
            assert(count == popcount_exec(abs_val));
            assert(popcount_exec(abs_val) == popcount(abs_val));
            assert(abs_val == abs_exec(xi));
            assert(abs_exec(xi) == abs_spec(xi));
            assert(count == popcount(abs_spec(xi)));
        }

        result.push(count);
    }
    result
}
// </vc-code>

}
fn main() {}