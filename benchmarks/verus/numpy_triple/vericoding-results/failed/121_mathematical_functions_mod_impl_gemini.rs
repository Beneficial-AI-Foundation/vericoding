// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [correct ensures to use mod_floor] */
fn numpy_mod_scalar(a: i8, b: i8) -> (result: i8)
    requires
        b != 0,
    ensures
        result as int == (a as int).mod_floor(b as int),
{
    if a == i8::MIN && b == -1 {
        proof {
            assert((i8::MIN as int).mod_floor(-1 as int) == 0) by(compute);
        }
        return 0i8;
    }

    let rem = a % b;
    if rem != 0 && (rem > 0) != (b > 0) {
        rem + b
    } else {
        rem
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [update invariant and add proof] */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < x2.len() as int ==> x2[j] != 0,
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] (result[j] as int) == (x1[j] as int).mod_floor(x2[j] as int),
        decreases x1.len() - i
    {
        let a = x1[i];
        let b = x2[i];
        
        let r = numpy_mod_scalar(a, b);

        result.push(r);
        i = i + 1;
    }

    proof {
        forall|k: int| 0 <= k < result.len() implies {
            let a = x1[k] as int;
            let b = x2[k] as int;
            vstd::math::lemma_mod_floor_properties(a, b);
            let r = result[k] as int;
            assert(r == a.mod_floor(b));
            assert(a == a.div_floor(b) * b + r);
            if b > 0 {
                assert(r >= 0 && r < b);
            } else {
                assert(r <= 0 && r > b);
            }
        }
    }

    result
}

// </vc-code>


}
fn main() {}