// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): handle overflow and fix invariants */
fn gcd_impl(a: i8, b: i8) -> (result: i8)
    requires a != i8::MIN, b != i8::MIN,
    ensures result as int == gcd(a as int, b as int),
            result >= 0,
            gcd(a as int, b as int) == gcd(int_abs(a as int), int_abs(b as int)),
            (a == 0 && b == 0) ==> result == 0,
            (a != 0 && b == 0) ==> result as int == int_abs(a as int),
            (a == 0 && b != 0) ==> result as int == int_abs(b as int),
            (result as int) % (a as int) == 0 && (result as int) % (b as int) == 0,
            gcd(b as int, a as int) == gcd(a as int, b as int),
{
    let mut x = if a >= 0 { a } else { -a };
    let mut y = if b >= 0 { b } else { -b };
    
    if x == 0 && y == 0 {
        return 0;
    }
    if x == 0 {
        return y;
    }
    if y == 0 {
        return x;
    }
    
    proof {
        assert(gcd(x as int, y as int) == gcd(a as int, b as int));
    }
    
    while y != 0
        invariant
            x >= 0,
            y >= 0,
            gcd(x as int, y as int) == gcd(a as int, b as int),
        decreases y,
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
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
    /* code modified by LLM (iteration 5): fix sequence indexing syntax */
    let mut result: Vec<i8> = Vec::new();
    
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1@.len(),
            x1@.len() == x2@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == gcd(x1@[j] as int, x2@[j] as int),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> gcd(x1@[j] as int, x2@[j] as int) == #[trigger] gcd(int_abs(x1@[j] as int), int_abs(x2@[j] as int)),
            forall|j: int| 0 <= j < i ==> (x1@[j] == 0 && x2@[j] == 0) ==> #[trigger] result@[j] == 0,
            forall|j: int| 0 <= j < i ==> (x1@[j] != 0 && x2@[j] == 0) ==> #[trigger] result@[j] as int == int_abs(x1@[j] as int),
            forall|j: int| 0 <= j < i ==> (x1@[j] == 0 && x2@[j] != 0) ==> #[trigger] result@[j] as int == int_abs(x2@[j] as int),
            forall|j: int| 0 <= j < i ==> #[trigger] (result@[j] as int) % (x1@[j] as int) == 0 && (result@[j] as int) % (x2@[j] as int) == 0,
            forall|j: int| 0 <= j < i ==> gcd(x2@[j] as int, x1@[j] as int) == #[trigger] gcd(x1@[j] as int, x2@[j] as int),
        decreases x1@.len() - i,
    {
        if x1[i as usize] != i8::MIN && x2[i as usize] != i8::MIN {
            let gcd_val = gcd_impl(x1[i as usize], x2[i as usize]);
            result.push(gcd_val);
        } else {
            result.push(0);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}