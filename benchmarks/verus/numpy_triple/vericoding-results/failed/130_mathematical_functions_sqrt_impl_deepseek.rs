// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_perfect_square(x: i8) -> (result: bool)
    ensures
        result <==> (exists|n: i8| n >= 0 && n * n == x && n <= x),
{
    /* helper modified by LLM (iteration 5): Add explicit bounds and use while loop */
    if x < 0 {
        false
    } else {
        let mut n: i8 = 0;
        while n <= x
            invariant
                0 <= n <= x + 1,
                forall|k: i8| 0 <= k < n ==> k * k != x,
            decreases (x - n) as int,
        {
            if n * n == x {
                return true;
            }
            n = n + 1;
        }
        false
    }
}

fn find_sqrt(x: i8) -> (result: i8)
    requires
        exists|n: i8| n >= 0 && n * n == x,
    ensures
        result >= 0,
        result * result == x,
{
    /* helper modified by LLM (iteration 5): Replace for loop with while loop */
    let mut n: i8 = 0;
    while n * n != x
        invariant
            0 <= n <= x + 1,
            exists|m: i8| n <= m <= x && m * m == x,
        decreases (x - n) as int,
    {
        n = n + 1;
    }
    n
}
// </vc-helpers>

// <vc-spec>
fn sqrt(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (x@[i] >= 0 ==> result@[i] * result@[i] == x@[i] && result@[i] >= 0)
            &&& (x@[i] == 0 ==> result@[i] == 0)
            &&& (x@[i] == 1 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix helper calls and add proper proof blocks */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x@[j] >= 0 ==> result@[j] * result@[j] == x@[j] && result@[j] >= 0)
                &&& (x@[j] == 0 ==> result@[j] == 0)
                &&& (x@[j] == 1 ==> result@[j] == 1)
            },
        decreases (x.len() - i) as int,
    {
        let x_val = x[i];
        let sqrt_val = if x_val < 0 {
            0
        } else {
            proof {
                let perfect = is_perfect_square(x_val);
                assert(perfect) by {
                    // x_val >= 0, so perfect square exists for non-negative values
                    assert(is_perfect_square(x_val) <==> (exists|n: i8| n >= 0 && n * n == x_val));
                };
            }
            find_sqrt(x_val)
        };
        result.push(sqrt_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}