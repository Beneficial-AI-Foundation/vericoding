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

proof fn product_base_case(numbers: Seq<u32>)
    requires numbers.len() == 1
    ensures product(numbers) == numbers[0]
{
}

proof fn product_recursive_case(numbers: Seq<u32>)
    requires numbers.len() > 1
    ensures product(numbers) == numbers[0] * product(numbers.subrange(1, numbers.len() as int))
{
}

proof fn product_subrange_ge_one(numbers: Seq<u32>)
    ensures product(numbers) >= 1
    decreases numbers.len()
{
    if numbers.len() == 0 {
    } else if numbers.len() == 1 {
        assert(numbers[0] >= 1);
    } else {
        product_subrange_ge_one(numbers.subrange(1, numbers.len() as int));
    }
}

proof fn product_overflow_lemma(numbers: Seq<u32>, acc: u64)
    requires
        acc <= u32::MAX,
        numbers.len() > 0,
        numbers[0] > 0,
        acc * numbers[0] > u32::MAX,
    ensures
        product(numbers) > u32::MAX,
    decreases numbers.len(),
{
    if numbers.len() == 1 {
        product_base_case(numbers);
        assert(product(numbers) == numbers[0]);
        assert(acc * numbers[0] > u32::MAX);
        assert(numbers[0] as u64 >= acc * numbers[0] as u64 / acc);
    } else {
        product_recursive_case(numbers);
        product_subrange_ge_one(numbers.subrange(1, numbers.len() as int));
        assert(product(numbers.subrange(1, numbers.len() as int)) >= 1);
        assert(product(numbers) >= numbers[0] * 1);
        assert(product(numbers) >= numbers[0]);
        assert(acc * numbers[0] > u32::MAX);
        assert(product(numbers) >= numbers[0] > u32::MAX);
    }
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
    let mut sum_acc: u64 = 0;
    let mut prod_acc: u64 = 1;
    let mut prod_valid = true;
    
    let mut i = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_acc == sum(numbers@.subrange(0, i as int)),
            prod_valid ==> prod_acc == product(numbers@.subrange(0, i as int)),
            prod_valid ==> prod_acc <= u32::MAX,
            sum_acc + sum(numbers@.subrange(i as int, numbers@.len() as int)) <= u64::MAX,
        decreases numbers.len() - i,
    {
        let num = numbers[i];
        
        proof {
            assert(sum(numbers@.subrange(0, (i + 1) as int)) == 
                   sum(numbers@.subrange(0, i as int)) + num);
        }
        
        sum_acc = sum_acc + num as u64;
        
        if prod_valid {
            if num == 0 || prod_acc <= u32::MAX as u64 / num as u64 {
                prod_acc = prod_acc * num as u64;
                if prod_acc > u32::MAX as u64 {
                    prod_valid = false;
                }
            } else {
                prod_valid = false;
            }
        }
        
        i = i + 1;
    }
    
    let final_product = if prod_valid && prod_acc <= u32::MAX as u64 {
        Some(prod_acc as u32)
    } else {
        None
    };
    
    (sum_acc, final_product)
}
// </vc-code>

}
fn main() {}