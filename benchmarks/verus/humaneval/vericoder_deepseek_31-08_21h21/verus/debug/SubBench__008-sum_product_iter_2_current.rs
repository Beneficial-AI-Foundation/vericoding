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
proof fn lemma_sum_empty() 
    ensures sum(Seq::empty()) == 0
{
    assert(sum(Seq::empty()) == 0);
}

proof fn lemma_sum_cons(numbers: Seq<u32>, x: u32)
    ensures sum(numbers.push(x)) == sum(numbers) + x
{
    assert(sum(numbers.push(x)) == sum(numbers) + x);
}

proof fn lemma_product_empty()
    ensures product(Seq::empty()) == 1
{
    assert(product(Seq::empty()) == 1);
}

proof fn lemma_product_cons(numbers: Seq<u32>, x: u32)
    ensures product(numbers.push(x)) == product(numbers) * x
{
    assert(product(numbers.push(x)) == product(numbers) * x);
}

proof fn lemma_product_zero(numbers: Seq<u32>, i: int)
    requires
        0 <= i < numbers.len(),
        numbers[i] == 0,
    ensures product(numbers) == 0
{
    if numbers.len() > 0 {
        if i == 0 {
            assert(product(numbers) == 0);
        } else {
            let prefix = numbers.subrange(0, i);
            lemma_product_zero(prefix.push(numbers[i]), i);
        }
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
    let mut sum_total: u64 = 0;
    let mut product_total: Option<u32> = Some(1);
    let mut index: usize = 0;
    
    while index < numbers.len()
        invariant
            index <= numbers.len(),
            sum_total == sum(numbers@.subrange(0, index as int)),
            product_total.is_some() ==> product_total.unwrap() == product(numbers@.subrange(0, index as int)),
            product_total.is_none() ==> product(numbers@.subrange(0, index as int)) == 0,
    {
        let current = numbers[index];
        sum_total = sum_total + current as u64;
        
        match product_total {
            Some(prod) => {
                let new_prod = prod.checked_mul(current);
                match new_prod {
                    Some(p) => {
                        product_total = Some(p);
                        proof {
                            lemma_product_cons(numbers@.subrange(0, index as int), current);
                        }
                    }
                    None => {
                        product_total = None;
                        proof {
                            lemma_product_zero(numbers@, index as int);
                        }
                    }
                }
            }
            None => {
            }
        }
        
        index = index + 1;
        
        proof {
            lemma_sum_cons(numbers@.subrange(0, (index - 1) as int), current);
        }
    }
    
    (sum_total, product_total)
}
// </vc-code>

fn main() {}
}