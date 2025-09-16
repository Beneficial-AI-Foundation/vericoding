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
/* helper modified by LLM (iteration 5): Added lemmas to prove sum and product properties */
proof fn sum_push_lemma(s: Seq<u32>, x: u32)
    ensures sum(s.push(x)) == sum(s) + x as int
{
    reveal(sum);
    s.push(x).fold_left_alt(0, |acc: int, y| acc + y, s.len() as int);
}

proof fn product_push_lemma(s: Seq<u32>, x: u32)
    ensures product(s.push(x)) == product(s) * x as int
{
    reveal(product);
    s.push(x).fold_left_alt(1, |acc: int, y| acc * y, s.len() as int);
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
    /* code modified by LLM (iteration 5): Fixed overflow tracking and added proper lemma calls */
    let mut sum_result: u64 = 0;
    let mut product_result: u32 = 1;
    let mut overflow = false;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_result as int == sum(numbers@.subrange(0, i as int)),
            !overflow ==> product_result as int == product(numbers@.subrange(0, i as int)),
            overflow ==> product(numbers@.subrange(0, i as int)) > u32::MAX as int,
        decreases numbers.len() - i
    {
        let old_sum = sum_result;
        sum_result = sum_result + numbers[i] as u64;
        
        proof {
            assert(numbers@.subrange(0, (i + 1) as int) =~= numbers@.subrange(0, i as int).push(numbers@[i as int]));
            sum_push_lemma(numbers@.subrange(0, i as int), numbers@[i as int]);
        }
        
        if !overflow {
            let temp = product_result as u64 * numbers[i] as u64;
            if temp > u32::MAX as u64 {
                overflow = true;
                proof {
                    product_push_lemma(numbers@.subrange(0, i as int), numbers@[i as int]);
                    assert(product(numbers@.subrange(0, (i + 1) as int)) == product(numbers@.subrange(0, i as int)) * numbers@[i as int] as int);
                    assert(product(numbers@.subrange(0, (i + 1) as int)) > u32::MAX as int);
                }
            } else {
                product_result = temp as u32;
                proof {
                    product_push_lemma(numbers@.subrange(0, i as int), numbers@[i as int]);
                }
            }
        } else {
            proof {
                product_push_lemma(numbers@.subrange(0, i as int), numbers@[i as int]);
                assert(product(numbers@.subrange(0, i as int)) > u32::MAX as int);
                assert(product(numbers@.subrange(0, (i + 1) as int)) > u32::MAX as int);
            }
        }
        
        i = i + 1;
    }
    
    assert(i == numbers.len());
    assert(numbers@.subrange(0, i as int) =~= numbers@);
    
    if overflow {
        (sum_result, None)
    } else {
        (sum_result, Some(product_result))
    }
}
// </vc-code>

}
fn main() {}