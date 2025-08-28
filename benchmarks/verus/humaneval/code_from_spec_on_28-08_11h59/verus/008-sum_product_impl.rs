use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end
// pure-end

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// pure-end

// <vc-helpers>
proof fn sum_bound(numbers: Seq<u32>)
    ensures
        sum(numbers) <= numbers.len() * u32::MAX,
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else {
        sum_bound(numbers.drop_last());
    }
}

proof fn sum_additive(numbers: Seq<u32>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        sum(numbers.subrange(0, i + 1)) == sum(numbers.subrange(0, i)) + numbers[i],
{
    let prefix = numbers.subrange(0, i);
    let next_prefix = numbers.subrange(0, i + 1);
    assert(next_prefix.drop_last() == prefix);
    assert(next_prefix.last() == numbers[i]);
}

proof fn sum_safe_cast(numbers: Seq<u32>, i: int)
    requires
        0 <= i <= numbers.len(),
        numbers.len() <= u32::MAX,
    ensures
        sum(numbers.subrange(0, i)) <= u64::MAX,
{
    sum_bound(numbers.subrange(0, i));
    assert(numbers.subrange(0, i).len() <= numbers.len());
    assert(sum(numbers.subrange(0, i)) <= numbers.subrange(0, i).len() * u32::MAX);
    assert(sum(numbers.subrange(0, i)) <= numbers.len() * u32::MAX);
    assert(numbers.len() * u32::MAX <= u64::MAX);
}

proof fn product_additive(numbers: Seq<u32>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        product(numbers.subrange(0, i + 1)) == product(numbers.subrange(0, i)) * numbers[i],
{
    let prefix = numbers.subrange(0, i);
    let next_prefix = numbers.subrange(0, i + 1);
    assert(next_prefix.drop_last() == prefix);
    assert(next_prefix.last() == numbers[i]);
}

proof fn product_overflow_lemma(numbers: Seq<u32>)
    ensures
        numbers.len() > 0 ==> (product(numbers) <= u32::MAX <==> (forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= u32::MAX) && product(numbers) <= u32::MAX),
    decreases numbers.len(),
{
}

proof fn multiplication_safety(a: u64, b: u64)
    requires
        a > 0,
        b > 0,
        a <= u64::MAX / b,
    ensures
        a * b <= u64::MAX,
{
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    // pre-conditions-start
    requires
        numbers.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut total_sum: u64 = 0;
    let mut total_product: u64 = 1;
    let mut product_overflow = false;
    
    for i in 0..numbers.len()
        invariant
            total_sum == sum(numbers@.subrange(0, i as int)),
            product_overflow || total_product == product(numbers@.subrange(0, i as int)),
            total_sum <= u64::MAX,
            total_product <= u64::MAX,
    {
        let num = numbers[i];
        
        proof {
            sum_additive(numbers@, i as int);
            sum_safe_cast(numbers@, i as int + 1);
            if !product_overflow {
                product_additive(numbers@, i as int);
            }
        }
        
        total_sum = total_sum + num as u64;
        
        if !product_overflow {
            if num == 0 {
                total_product = 0;
            } else if total_product > u64::MAX / (num as u64) {
                product_overflow = true;
            } else {
                proof {
                    multiplication_safety(total_product, num as u64);
                }
                total_product = total_product * (num as u64);
            }
        }
    }
    
    let final_product = if product_overflow || total_product > u32::MAX as u64 {
        None
    } else {
        Some(total_product as u32)
    };
    
    (total_sum, final_product)
}
// </vc-code>

}
fn main() {}