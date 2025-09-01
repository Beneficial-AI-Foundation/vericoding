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
#[verifier::truncate]
spec fn to_u64(x: int) -> u64 {
    x as u64
}

#[verifier::truncate]
spec fn to_u32(x: int) -> u32 {
    x as u32
}

#[verifier::truncate]
fn add_u64(a: u64, b: u64) -> u64 {
    a + b
}

#[verifier::truncate]
fn mul_u64(a: u64, b: u64) -> u64 {
    a * b
}

proof fn lemma_product_step(s: Seq<u32>, i: int)
    requires 0 <= i < s.len()
    ensures product(s.subrange(0, i+1)) == product(s.subrange(0, i)) * s[i]
{
    // By definition of fold_left for sequences
    let prefix = s.subrange(0, i);
    let new_seq = prefix.push(s[i]);
    assert(new_seq == s.subrange(0, i+1));
    assert(product(new_seq) == product(prefix) * s[i]);
}

proof fn lemma_sum_step(s: Seq<u32>, i: int)
    requires 0 <= i < s.len()
    ensures sum(s.subrange(0, i+1)) == sum(s.subrange(0, i)) + s[i]
{
    // By definition of fold_left for sequences
    let prefix = s.subrange(0, i);
    let new_seq = prefix.push(s[i]);
    assert(new_seq == s.subrange(0, i+1));
    assert(sum(new_seq) == sum(prefix) + s[i]);
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
    let mut product_acc: Option<u32> = Some(1);

    for i in 0..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum_acc == to_u64(sum(numbers@.subrange(0, i as int))),
            product_acc == 
                if product(numbers@.subrange(0, i as int)) <= (u32::MAX as int) {
                    Some(to_u32(product(numbers@.subrange(0, i as int))))
                } else {
                    None
                }
    {
        let num = numbers[i];
        proof {
            lemma_sum_step(numbers@, i as int);
            lemma_product_step(numbers@, i as int);
        }

        sum_acc = add_u64(sum_acc, num as u64);

        product_acc = match product_acc {
            Some(p) => {
                let p_u64 = p as u64;
                let num_u64 = num as u64;
                let new_product_u64 = mul_u64(p_u64, num_u64);
                if new_product_u64 <= (u32::MAX as u64) {
                    Some(new_product_u64 as u32)
                } else {
                    None
                }
            },
            None => {
                if num == 0 {
                    Some(0)
                } else {
                    None
                }
            }
        };
    }

    (sum_acc, product_acc)
}
// </vc-code>

fn main() {}
}