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
    ensures
        sum(Seq::empty()) == 0,
{
    assert(sum(Seq::empty()) == 0);
}

proof fn lemma_sum_cons(x: u32, s: Seq<u32>)
    ensures
        sum(s.push(x)) == sum(s) + (x as int),
{
    assert(sum(s.push(x)) == sum(s) + (x as int));
}

proof fn lemma_product_empty() 
    ensures
        product(Seq::empty()) == 1,
{
    assert(product(Seq::empty()) == 1);
}

proof fn lemma_product_cons(x: u32, s: Seq<u32>)
    ensures
        product(s.push(x)) == product(s) * (x as int),
{
    assert(product(s.push(x)) == product(s) * (x as int));
}

spec fn should_compute_product(n: Seq<u32>) -> bool {
    product(n) <= (u32::MAX as int)
}

proof fn lemma_product_bound(s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        product(s.subrange(0, i as usize)) <= (u32::MAX as int) as int || !should_compute_product(s.subrange(0, i as usize)),
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
    // impl-start
    let mut sum: u64 = 0;
    let mut product: Option<u32> = Some(1);
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum == sum(numbers@.subrange(0, i)),
            product.is_some() ==> product == Some(product(numbers@.subrange(0, i)) as u32),
            product.is_none() ==> !should_compute_product(numbers@.subrange(0, i)),
    {
        let x = numbers[i];
        sum = sum + (x as u64);
        
        match product {
            Some(p) => {
                let new_product = (p as u64) * (x as u64);
                if new_product <= (u32::MAX as u64) {
                    product = Some(new_product as u32);
                } else {
                    product = None;
                }
            }
            None => {}
        }
        
        i = i + 1;
    }
    
    (sum, product)
    // impl-end
}
// </vc-code>

fn main() {}
}