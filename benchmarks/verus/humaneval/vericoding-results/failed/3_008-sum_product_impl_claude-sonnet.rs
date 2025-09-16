// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by removing int casts in exec code */
fn safe_add_u64(a: u64, b: u32) -> (result: u64)
    requires
        a as int + b as int <= u64::MAX,
    ensures
        result as int == a as int + b as int,
{
    a + b as u64
}

fn safe_mul_u32(a: u32, b: u32) -> (result: Option<u32>)
    ensures
        result matches Some(v) ==> v as int == a as int * b as int,
        result matches None ==> a as int * b as int > u32::MAX,
{
    if a == 0 || b == 0 {
        Some(0)
    } else {
        proof {
            assert(a as int * b as int <= u32::MAX || a as int * b as int > u32::MAX);
        }
        if a <= u32::MAX / b {
            Some(a * b)
        } else {
            None
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))

    requires
        numbers.len() < u32::MAX,

    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors and improved overflow checking */
    let mut sum_result: u64 = 0;
    let mut product_result: Option<u32> = Some(1);
    
    let mut i = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_result == sum(numbers@.subrange(0, i as int)),
            product_result matches Some(v) ==> v as int == product(numbers@.subrange(0, i as int)),
            product_result matches None ==> product(numbers@.subrange(0, i as int)) > u32::MAX,
            sum_result as int + sum(numbers@.subrange(i as int, numbers.len() as int)) <= u64::MAX,
        decreases numbers.len() - i
    {
        let num = numbers[i];
        
        proof {
            assert(sum(numbers@.subrange(0, (i+1) as int)) == sum(numbers@.subrange(0, i as int)) + num as int);
        }
        
        sum_result = safe_add_u64(sum_result, num);
        
        if let Some(current_product) = product_result {
            proof {
                assert(product(numbers@.subrange(0, (i+1) as int)) == product(numbers@.subrange(0, i as int)) * num as int);
            }
            product_result = safe_mul_u32(current_product, num);
        }
        
        i += 1;
    }
    
    (sum_result, product_result)
}
// </vc-code>

}
fn main() {}