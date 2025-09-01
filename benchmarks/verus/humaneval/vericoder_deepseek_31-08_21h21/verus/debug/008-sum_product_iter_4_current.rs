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
        product(s.subrange(0, i)) <= (u32::MAX as int) as int || !should_compute_product(s.subrange(0, i)),
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
    let mut sum_val: u64 = 0;
    let mut product_val: Option<u32> = Some(1);
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_val == sum(numbers@.subrange(0, i as int)),
            product_val.is_some() ==> product_val == Some(product(numbers@.subrange(0, i as int)) as u32),
            product_val.is_none() ==> !should_compute_product(numbers@.subrange(0, i as int)),
        decreases numbers.len() - i
    {
        let x = numbers[i];
        sum_val = sum_val + (x as u64);
        
        match product_val {
            Some(p) => {
                let new_product = (p as u64) * (x as u64);
                if new_product <= (u32::MAX as u64) {
                    product_val = Some(new_product as u32);
                } else {
                    product_val = None;
                }
            }
            None => {}
        }
        
        i = i + 1;
    }
    
    (sum_val, product_val)
}
// </vc-code>

fn main() {}
}