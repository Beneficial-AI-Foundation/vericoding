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
/* helper modified by LLM (iteration 5): spec helpers and lemmas for i8 sequences */
spec fn sum_magnitudes_i8(arr: Seq<i8>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 0 } else { abs(arr[0] as int) + sum_magnitudes_i8(arr.subrange(1, arr.len() as int)) }
}

/* helper modified by LLM (iteration 5): product of signs over Seq<i8> */
spec fn product_signs_i8(arr: Seq<i8>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 1 } else { sign(arr[0] as int) * product_signs_i8(arr.subrange(1, arr.len() as int)) }
}

/* helper modified by LLM (iteration 5): lemma equating sum specs for Seq<i8> and mapped Seq<int> */
proof fn lemma_sum_magnitudes_i8_vs_int_map(arr: Seq<i8>)
    ensures
        sum_magnitudes_i8(arr) == sum_of_magnitudes(arr.map(|i: int, x: i8| x as int)),
    decreases arr.len()
{
    if arr.len() == 0 {
        assert(sum_magnitudes_i8(arr) == 0);
        assert(sum_of_magnitudes(arr.map(|i: int, x: i8| x as int)) == 0);
        assert(sum_magnitudes_i8(arr) == sum_of_magnitudes(arr.map(|i: int, x: i8| x as int)));
    } else {
        lemma_sum_magnitudes_i8_vs_int_map(arr.subrange(1, arr.len() as int));
        assert(arr.map(|i: int, x: i8| x as int).len() == arr.len());
        assert(arr.map(|i: int, x: i8| x as int)[0] == arr[0] as int);
        assert(
            arr.map(|i: int, x: i8| x as int).subrange(1, arr.len() as int)
            == arr.subrange(1, arr.len() as int).map(|i: int, x: i8| x as int)
        );
        assert(sum_magnitudes_i8(arr)
            == abs(arr[0] as int) + sum_magnitudes_i8(arr.subrange(1, arr.len() as int)));
        assert(sum_of_magnitudes(arr.map(|i: int, x: i8| x as int))
            == abs(arr.map(|i: int, x: i8| x as int)[0])
               + sum_of_magnitudes(arr.map(|i: int, x: i8| x as int).subrange(1, arr.len() as int)));
        assert(sum_magnitudes_i8(arr) == sum_of_magnitudes(arr.map(|i: int, x: i8| x as int)));
    }
}

/* helper modified by LLM (iteration 5): lemma equating product specs for Seq<i8> and mapped Seq<int> */
proof fn lemma_product_signs_i8_vs_int_map(arr: Seq<i8>)
    ensures
        product_signs_i8(arr) == product_of_signs(arr.map(|i: int, x: i8| x as int)),
    decreases arr.len()
{
    if arr.len() == 0 {
        assert(product_signs_i8(arr) == 1);
        assert(product_of_signs(arr.map(|i: int, x: i8| x as int)) == 1);
        assert(product_signs_i8(arr) == product_of_signs(arr.map(|i: int, x: i8| x as int)));
    } else {
        lemma_product_signs_i8_vs_int_map(arr.subrange(1, arr.len() as int));
        assert(arr.map(|i: int, x: i8| x as int).len() == arr.len());
        assert(arr.map(|i: int, x: i8| x as int)[0] == arr[0] as int);
        assert(
            arr.map(|i: int, x: i8| x as int).subrange(1, arr.len() as int)
            == arr.subrange(1, arr.len() as int).map(|i: int, x: i8| x as int)
        );
        assert(product_signs_i8(arr)
            == sign(arr[0] as int) * product_signs_i8(arr.subrange(1, arr.len() as int)));
        assert(product_of_signs(arr.map(|i: int, x: i8| x as int))
            == sign(arr.map(|i: int, x: i8| x as int)[0])
               * product_of_signs(arr.map(|i: int, x: i8| x as int).subrange(1, arr.len() as int)));
        assert(product_signs_i8(arr) == product_of_signs(arr.map(|i: int, x: i8| x as int)));
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
    /* code modified by LLM (iteration 5): compute result via spec expressions and cast using `as i8` */
    if arr.len() == 0usize {
        Option::<i8>::None
    } else {
        proof {
            lemma_sum_magnitudes_i8_vs_int_map(arr@);
            lemma_product_signs_i8_vs_int_map(arr@);
        }
        let res: i8 = (sum_magnitudes_i8(arr@) * product_signs_i8(arr@)) as i8;
        Option::<i8>::Some(res)
    }
}
// </vc-code>


}

fn main() {}