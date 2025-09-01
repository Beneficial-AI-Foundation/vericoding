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
    ensures sum(Seq::<u32>::empty()) == 0
{
}

proof fn lemma_sum_one(x: u32)
    ensures sum(seq![x]) == x
{
}

proof fn lemma_sum_append(s1: Seq<u32>, s2: Seq<u32>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
}

proof fn lemma_product_empty()
    ensures product(Seq::<u32>::empty()) == 1
{
}

proof fn lemma_product_one(x: u32)
    ensures product(seq![x]) == x
{
}

proof fn lemma_product_append(s1: Seq<u32>, s2: Seq<u32>)
    ensures product(s1 + s2) == product(s1) * product(s2)
{
}

proof fn lemma_sum_push(s: Seq<u32>, x: u32)
    ensures sum(s.push(x)) == sum(s) + x
{
    assert(s.push(x) == s + seq![x]);
    lemma_sum_append(s, seq![x]);
    lemma_sum_one(x);
}

proof fn lemma_product_push(s: Seq<u32>, x: u32)
    ensures product(s.push(x)) == product(s) * x
{
    assert(s.push(x) == s + seq![x]);
    lemma_product_append(s, seq![x]);
    lemma_product_one(x);
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
    
    proof {
        lemma_sum_empty();
        lemma_product_empty();
    }
    
    for i in 0..numbers.len()
        invariant
            total_sum == sum(numbers@.subrange(0, i as int)),
            !product_overflow ==> total_product == product(numbers@.subrange(0, i as int)),
            total_product <= u32::MAX || product_overflow,
    {
        let num = numbers[i];
        
        proof {
            lemma_sum_push(numbers@.subrange(0, i as int), num);
            assert(numbers@.subrange(0, i as int).push(num) == numbers@.subrange(0, i as int + 1));
        }
        
        total_sum = total_sum + num as u64;
        
        if !product_overflow {
            if num == 0 || total_product > u32::MAX as u64 / num as u64 {
                product_overflow = true;
            } else {
                proof {
                    lemma_product_push(numbers@.subrange(0, i as int), num);
                    assert(numbers@.subrange(0, i as int).push(num) == numbers@.subrange(0, i as int + 1));
                }
                total_product = total_product * num as u64;
            }
        }
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) == numbers@);
    }
    
    let product_result = if product_overflow {
        None
    } else {
        Some(total_product as u32)
    };
    
    (total_sum, product_result)
}
// </vc-code>

fn main() {}
}