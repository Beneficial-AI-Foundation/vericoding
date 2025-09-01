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
proof fn sum_empty()
    ensures sum(Seq::<u32>::empty()) == 0
{
    assert(Seq::<u32>::empty().fold_left(0, |acc: int, x| acc + x) == 0);
}

proof fn sum_push(s: Seq<u32>, x: u32)
    ensures sum(s.push(x)) == sum(s) + x
{
    reveal(Seq::fold_left);
    assert(s.push(x).fold_left(0, |acc: int, x| acc + x) == 
           s.fold_left(0, |acc: int, x| acc + x) + x);
}

proof fn product_empty()
    ensures product(Seq::<u32>::empty()) == 1
{
    assert(Seq::<u32>::empty().fold_left(1, |acc: int, x| acc * x) == 1);
}

proof fn product_push(s: Seq<u32>, x: u32)
    ensures product(s.push(x)) == product(s) * x
{
    reveal(Seq::fold_left);
    assert(s.push(x).fold_left(1, |acc: int, x| acc * x) == 
           s.fold_left(1, |acc: int, x| acc * x) * x);
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
    let mut sum_val: u64 = 0;
    let mut prod_val: u32 = 1;
    let mut prod_overflow = false;
    
    for i in 0..numbers.len()
        invariant
            i <= numbers.len(),
            sum_val == sum(numbers@.take(i as int)),
            !prod_overflow ==> prod_val == product(numbers@.take(i as int)),
    {
        let val = numbers[i];
        
        // Update sum
        proof {
            assert(numbers@.take(i as int).push(val) =~= numbers@.take((i + 1) as int));
            sum_push(numbers@.take(i as int), val);
        }
        sum_val = sum_val + val as u64;
        
        // Update product if not overflowed
        if !prod_overflow {
            match prod_val.checked_mul(val) {
                Some(new_prod) => {
                    proof {
                        product_push(numbers@.take(i as int), val);
                    }
                    prod_val = new_prod;
                },
                None => {
                    prod_overflow = true;
                }
            }
        }
    }
    
    proof {
        assert(numbers@.take(numbers.len() as int) =~= numbers@);
    }
    
    if prod_overflow {
        (sum_val, None)
    } else {
        (sum_val, Some(prod_val))
    }
}
// </vc-code>

fn main() {}
}