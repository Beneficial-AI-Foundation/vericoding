// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_conversion(x: int)
        requires x >= -128 && x <= 127,
        ensures (x as i8) as int == x
    {
        // Built-in conversion property
    }

    fn cumulative_product(a: Vec<i8>, n: int) -> int
        requires 0 <= n <= a.len(),
        ensures n == 0 ==> result == 1,
        ensures n > 0 ==> result == {
            let mut prod = a[0] as int;
            let mut i = 1;
            while i < n
                invariant 1 <= i <= n,
                invariant prod == cumulative_product(a, i)
            {
                prod = prod * (a[i] as int);
                i += 1;
            }
            prod
        }
    {
        if n == 0 {
            1
        } else {
            let mut prod = a[0] as int;
            let mut i = 1;
            while i < n
                invariant 1 <= i <= n,
                invariant prod == cumulative_product(a, i)
            {
                prod = prod * (a[i] as int);
                i += 1;
            }
            prod
        }
    }
// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
{
        let mut result = Vec::new();
        result.push(a[0]);
        let mut current: int = a[0] as int;
        let mut i = 1;
        while i < a.len()
            invariant
                result.len() == i,
                forall|j: int| 0 < j < i ==> result[j] as int == result[j-1] as int * a[j] as int,
                current == cumulative_product(a, i),
                current >= -128 && current <= 127,
            decreases a.len() - i
        {
            current = current * (a[i] as int);
            proof {
                lemma_i8_conversion(current);
            }
            let next = current as i8;
            result.push(next);
            i += 1;
        }
        result
    }
// </vc-code>


}
fn main() {}