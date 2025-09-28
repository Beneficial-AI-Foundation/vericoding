// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn divides(d: int, n: int) -> bool {
    exists|k: int| n == d * k
}

/* helper modified by LLM (iteration 5): moved compute_gcd to spec function to resolve compilation error */
spec fn compute_gcd(a: i8, b: i8) -> i8 {
    let mut x = if a >= 0 { a } else { -a };
    let mut y = if b >= 0 { b } else { -b };
    if y == 0 {
        x
    } else {
        compute_gcd(y, x % y)
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::external_body]
spec fn gcd(a: int, b: int) -> int {
    unimplemented!()
}

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1@.len() == x2@.len(),
    ensures
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == gcd(x1@[i] as int, x2@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= 0,
        forall|i: int| 0 <= i < result@.len() ==> gcd(x1@[i] as int, x2@[i] as int) == #[trigger] gcd(int_abs(x1@[i] as int), int_abs(x2@[i] as int)),
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] == 0 && x2@[i] == 0) ==> #[trigger] result@[i] == 0,
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] != 0 && x2@[i] == 0) ==> #[trigger] result@[i] as int == int_abs(x1@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> (x1@[i] == 0 && x2@[i] != 0) ==> #[trigger] result@[i] as int == int_abs(x2@[i] as int),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] (result@[i] as int) % (x1@[i] as int) == 0 && (result@[i] as int) % (x2@[i] as int) == 0,
        forall|i: int| 0 <= i < result@.len() ==> gcd(x2@[i] as int, x1@[i] as int) == #[trigger] gcd(x1@[i] as int, x2@[i] as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced compute_gcd with gcd in postconditions */
    let mut result = Vec::with_capacity(x1.len());
    for i in 0..x1.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == gcd(x1@[j] as int, x2@[j] as int),
        decreases x1.len() - i
    {
        let a = x1[i];
        let b = x2[i];
        let g = if b == 0 {
            if a >= 0 { a } else { -a }
        } else if a == 0 {
            if b >= 0 { b } else { -b }
        } else {
            let mut x = if a >= 0 { a } else { -a };
            let mut y = if b >= 0 { b } else { -b };
            while y != 0 {
                let temp = y;
                y = x % y;
                x = temp;
            }
            x
        };
        result.push(g);
    }
    result
}
// </vc-code>

}
fn main() {}