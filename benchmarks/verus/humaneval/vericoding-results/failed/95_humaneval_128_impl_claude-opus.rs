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
proof fn lemma_sum_of_magnitudes_step(arr: Seq<int>, sum: int, i: nat)
    requires
        i < arr.len(),
        sum == sum_of_magnitudes(arr.subrange(0, i as int)),
    ensures
        sum + abs(arr[i as int]) == sum_of_magnitudes(arr.subrange(0, (i + 1) as int)),
{
    /* helper modified by LLM (iteration 5): simplified proof structure */
    let sub_i = arr.subrange(0, i as int);
    let sub_i_plus_1 = arr.subrange(0, (i + 1) as int);
    
    if i == 0 {
        assert(sub_i.len() == 0);
        assert(sum_of_magnitudes(sub_i) == 0);
        assert(sub_i_plus_1.len() == 1);
        assert(sub_i_plus_1[0] == arr[0]);
        assert(sum_of_magnitudes(sub_i_plus_1) == abs(arr[0]));
    } else {
        assert(sub_i_plus_1 =~= sub_i.push(arr[i as int]));
    }
}

proof fn lemma_product_of_signs_step(arr: Seq<int>, prod: int, i: nat)
    requires
        i < arr.len(),
        prod == product_of_signs(arr.subrange(0, i as int)),
    ensures
        prod * sign(arr[i as int]) == product_of_signs(arr.subrange(0, (i + 1) as int)),
{
    /* helper modified by LLM (iteration 5): simplified proof structure */
    let sub_i = arr.subrange(0, i as int);
    let sub_i_plus_1 = arr.subrange(0, (i + 1) as int);
    
    if i == 0 {
        assert(sub_i.len() == 0);
        assert(product_of_signs(sub_i) == 1);
        assert(sub_i_plus_1.len() == 1);
        assert(sub_i_plus_1[0] == arr[0]);
        assert(product_of_signs(sub_i_plus_1) == sign(arr[0]));
    } else {
        assert(sub_i_plus_1 =~= sub_i.push(arr[i as int]));
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
    /* code modified by LLM (iteration 5): fixed type conversion issue by using spec function in ghost context */
    if arr.len() == 0 {
        return Option::<i8>::None;
    }
    
    let ghost arr_seq = arr@.map(|j: int, x: i8| x as int);
    let mut sum: i32 = 0;
    let mut prod: i32 = 1;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum >= 0,
            sum <= i * 127,
            sum == sum_of_magnitudes(arr_seq.subrange(0, i as int)) as i32,
            prod == product_of_signs(arr_seq.subrange(0, i as int)) as i32,
            prod == 1 || prod == -1 || prod == 0,
        decreases arr.len() - i
    {
        let val = arr[i] as i32;
        let abs_val = if val >= 0 { val } else { -val };
        let sign_val = if val > 0 { 1 } else if val < 0 { -1 } else { 0 };
        
        proof {
            assert(arr_seq[i as int] == arr[i] as int);
            assert(abs_val == abs(arr_seq[i as int]));
            assert(sign_val == sign(arr_seq[i as int]));
            lemma_sum_of_magnitudes_step(arr_seq, sum as int, i as nat);
            lemma_product_of_signs_step(arr_seq, prod as int, i as nat);
        }
        
        sum = sum + abs_val;
        prod = prod * sign_val;
        i = i + 1;
    }
    
    assert(arr_seq.subrange(0, arr.len() as int) =~= arr_seq);
    assert(sum == sum_of_magnitudes(arr_seq) as i32);
    assert(prod == product_of_signs(arr_seq) as i32);
    
    let result = (sum * prod) as i8;
    Option::<i8>::Some(result)
}
// </vc-code>


}

fn main() {}