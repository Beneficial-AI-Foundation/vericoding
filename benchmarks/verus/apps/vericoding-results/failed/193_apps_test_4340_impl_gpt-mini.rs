// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn transform_element(x: int) -> int {
    if x % 2 == 0 { x - 1 } else { x }
}

spec fn valid_transformation(input: Seq<int>, output: Seq<int>) -> bool {
    output.len() == input.len() &&
    forall|i: int| 0 <= i < input.len() ==> output[i] == transform_element(input[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): convert i8 to transformed i8 matching transform_element */
fn transform_i8(x: i8) -> i8
    ensures
        (transform_i8(x) as int) == transform_element(x as int),
{
    if x % 2 == 0 {
        x - 1
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate over input and apply transform_i8 to each element */
    let n = a.len();
    let mut res: Vec<i8> = Vec::new();
    res.reserve(n);

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> (
                (res@.map(|_k, y: i8| y as int)@[j] == transform_element(a@.map(|_k, y: i8| y as int)@[j]))
            ),
        decreases (n - i) as nat
    {
        let x = a[i];
        let y = transform_i8(x);
        res.push(y);
        i += 1;
    }

    res
}
// </vc-code>


}

fn main() {}