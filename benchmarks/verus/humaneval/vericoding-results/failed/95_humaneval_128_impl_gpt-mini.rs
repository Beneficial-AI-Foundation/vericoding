// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn sign(x: int) -> int {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

spec fn sum_of_magnitudes(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 0 } else { abs(arr[0]) + sum_of_magnitudes(arr.subrange(1, arr.len() as int)) }
}

spec fn product_of_signs(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 1 } else { sign(arr[0]) * product_of_signs(arr.subrange(1, arr.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Prove sum_of_magnitudes and product_of_signs by recursion */
proof fn seq_sum_prod_int(s: Seq<int>)
{
    if s.len() == 0 {
        assert(sum_of_magnitudes(s) == 0);
        assert(product_of_signs(s) == 1);
    } else {
        let tail = s.subrange(1, s.len());
        seq_sum_prod_int(tail);
        assert(sum_of_magnitudes(s) == abs(s[0]) + sum_of_magnitudes(tail));
        assert(product_of_signs(s) == sign(s[0]) * product_of_signs(tail));
    }
}
// </vc-helpers>

// <vc-spec>
fn prod_signs(arr: Vec<i8>) -> (result: Option<i8>)
    ensures 
        (arr@.len() == 0) ==> (result == Option::<i8>::None) &&
        (arr@.len() > 0) ==> (result == Option::<i8>::Some((sum_of_magnitudes(arr@.map(|i: int, x: i8| x as int)) * product_of_signs(arr@.map(|i: int, x: i8| x as int))) as i8))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Compute sum and product using i64 loop without spec-int casts; prove equality in a proof block after loop */
    if arr.len() == 0 {
        Option::<i8>::None
    } else {
        let n: usize = arr.len();
        let mut i: usize = n;
        let mut s: i64 = 0;
        let mut p: i64 = 1;
        while i > 0
            invariant
                i <= n,
            decreases i
        {
            let i1 = i - 1;
            let x_i64: i64 = arr[i1] as i64;
            s = s + (if x_i64 >= 0 { x_i64 } else { -x_i64 });
            p = p * (if x_i64 > 0 { 1 } else if x_i64 < 0 { -1 } else { 0 });
            i = i1;
        }
        let v_i64: i64 = s * p;
        proof {
            let seq: Seq<int> = arr@.map(|j: int, y: i8| y as int);
            seq_sum_prod_int(seq);
            assert((sum_of_magnitudes(seq) * product_of_signs(seq)) as i64 == v_i64);
        }
        let v: i8 = v_i64 as i8;
        Option::<i8>::Some(v)
    }
}
// </vc-code>


}

fn main() {}