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

proof fn lemma_sum_push(s: Seq<u32>, x: u32)
    ensures sum(s.push(x)) == sum(s) + x
{
    assert(s.push(x).fold_left(0, |acc: int, y| acc + y) == sum(s) + x) by {
        s.push(x).lemma_fold_left_alt(0, |acc: int, y| acc + y);
    }
}

proof fn lemma_product_empty()
    ensures product(Seq::<u32>::empty()) == 1
{
}

proof fn lemma_product_push(s: Seq<u32>, x: u32)
    ensures product(s.push(x)) == product(s) * x
{
    assert(s.push(x).fold_left(1, |acc: int, y| acc * y) == product(s) * x) by {
        s.push(x).lemma_fold_left_alt(1, |acc: int, y| acc * y);
    }
}

proof fn lemma_sum_prefix(s: Seq<u32>, i: int)
    requires 0 <= i <= s.len()
    ensures sum(s.subrange(0, i)) == s.subrange(0, i).fold_left(0, |acc: int, x| acc + x)
{
}

proof fn lemma_product_prefix(s: Seq<u32>, i: int)
    requires 0 <= i <= s.len()
    ensures product(s.subrange(0, i)) == s.subrange(0, i).fold_left(1, |acc: int, x| acc * x)
{
}

proof fn lemma_sum_extend(s: Seq<u32>, i: int)
    requires 0 <= i < s.len()
    ensures sum(s.subrange(0, i + 1)) == sum(s.subrange(0, i)) + s[i]
{
    assert(s.subrange(0, i + 1) =~= s.subrange(0, i).push(s[i]));
    lemma_sum_push(s.subrange(0, i), s[i]);
}

proof fn lemma_product_extend(s: Seq<u32>, i: int)
    requires 0 <= i < s.len()
    ensures product(s.subrange(0, i + 1)) == product(s.subrange(0, i)) * s[i]
{
    assert(s.subrange(0, i + 1) =~= s.subrange(0, i).push(s[i]));
    lemma_product_push(s.subrange(0, i), s[i]);
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
    let mut total_product: u32 = 1;
    let mut product_overflow = false;
    
    for i in 0..numbers.len()
        invariant
            i <= numbers.len(),
            total_sum == sum(numbers@.subrange(0, i as int)),
            !product_overflow ==> total_product == product(numbers@.subrange(0, i as int)),
            total_sum <= u64::MAX - u32::MAX,
    {
        proof {
            lemma_sum_extend(numbers@, i as int);
        }
        total_sum = total_sum + numbers[i] as u64;
        
        if !product_overflow {
            match total_product.checked_mul(numbers[i]) {
                Some(new_product) => {
                    total_product = new_product;
                    proof {
                        lemma_product_extend(numbers@, i as int);
                    }
                }
                None => {
                    product_overflow = true;
                }
            }
        }
    }
    
    let final_product = if product_overflow {
        None
    } else {
        Some(total_product)
    };
    
    (total_sum, final_product)
}
// </vc-code>

fn main() {}
}