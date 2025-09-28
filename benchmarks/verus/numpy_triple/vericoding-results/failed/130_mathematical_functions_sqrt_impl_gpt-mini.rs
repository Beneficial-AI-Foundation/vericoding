// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): linear search for integer sqrt */
fn find_sqrt(x: i8) -> (result: i8)
    requires
        x >= 0,
    ensures
        result * result == x,
{
    let mut r: i8 = 0;
    let mut result: i8 = 0;
    while r <= 11
        invariant
            0 <= r && r <= 11,
        decreases 12 - (r as int)
    {
        if r * r == x {
            result = r;
            return result;
        }
        r = r + 1;
    }
    result = 0;
    result
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
    /* code modified by LLM (iteration 5): iterate over vector and use find_sqrt for nonnegative entries */
    let n: nat = x@.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant
            res@.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> {
                &&& (x@[j] >= 0 ==> res@[j] * res@[j] == x@[j] && res@[j] >= 0)
                &&& (x@[j] == 0 ==> res@[j] == 0)
                &&& (x@[j] == 1 ==> res@[j] == 1)
            },
        decreases n - i
    {
        let xi: i8 = x@[(i as int)];
        if xi >= 0 {
            let r: i8 = find_sqrt(xi);
            res.push(r);
        } else {
            res.push(0);
        }
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}