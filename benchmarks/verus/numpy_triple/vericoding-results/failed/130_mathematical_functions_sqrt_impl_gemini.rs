// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Replaced `unreachable!` with Verus's `unreached()`.] */
fn sqrt_inner(n: i8) -> (r: i8)
    requires
        0 <= n,
        exists|k: i8| k >= 0 && (k as int) * (k as int) == (n as int),
    ensures
        r >= 0,
        (r as int) * (r as int) == (n as int),
{
    let mut i: i8 = 0;
    while i <= 11
        invariant
            0 <= i <= 12,
            (exists|k: i8| k >= 0 && (k as int) * (k as int) == (n as int)),
            forall|j: i8| 0 <= j < i ==> (j as int) * (j as int) != (n as int),
        decreases 12 - i,
    {
        if i * i == n {
            return i;
        }
        i = i + 1;
    }
    unreached();
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
/* code modified by LLM (iteration 5): [Added assertion to make sqrt_inner precondition explicit.] */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let xj = x@[j];
                let rj: i8 = result@[j];
                &&& (xj >= 0 ==> (rj as int) * (rj as int) == (xj as int) && rj >= 0)
                &&& (xj == 0 ==> rj == 0)
                &&& (xj == 1 ==> rj == 1)
            },
        decreases x.len() - i,
    {
        let val = x[i];
        let r: i8;
        if val >= 0 {
            proof {
                assert(exists|k: i8| k >= 0 && (k as int) * (k as int) == (val as int));
            }
            r = sqrt_inner(val);
        } else {
            r = 0;
        }
        result.push(r);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}