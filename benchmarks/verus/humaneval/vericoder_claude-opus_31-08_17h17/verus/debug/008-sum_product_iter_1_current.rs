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
proof fn sum_fold_left_step(s: Seq<u32>, i: nat)
    requires
        i < s.len(),
    ensures
        s.subrange(0, (i + 1) as int).fold_left(0, |acc: int, x| acc + x) 
        == s.subrange(0, i as int).fold_left(0, |acc: int, x| acc + x) + s[i as int],
{
    let s1 = s.subrange(0, i as int);
    let s2 = s.subrange(0, (i + 1) as int);
    assert(s2 =~= s1.push(s[i as int]));
}

proof fn product_fold_left_step(s: Seq<u32>, i: nat)
    requires
        i < s.len(),
    ensures
        s.subrange(0, (i + 1) as int).fold_left(1, |acc: int, x| acc * x) 
        == s.subrange(0, i as int).fold_left(1, |acc: int, x| acc * x) * s[i as int],
{
    let s1 = s.subrange(0, i as int);
    let s2 = s.subrange(0, (i + 1) as int);
    assert(s2 =~= s1.push(s[i as int]));
}

proof fn sum_fold_left_complete(s: Seq<u32>)
    ensures
        s.fold_left(0, |acc: int, x| acc + x) == s.subrange(0, s.len() as int).fold_left(0, |acc: int, x| acc + x),
{
    assert(s =~= s.subrange(0, s.len() as int));
}

proof fn product_fold_left_complete(s: Seq<u32>)
    ensures
        s.fold_left(1, |acc: int, x| acc * x) == s.subrange(0, s.len() as int).fold_left(1, |acc: int, x| acc * x),
{
    assert(s =~= s.subrange(0, s.len() as int));
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
    let mut sum_result: u64 = 0;
    let mut product_result: u32 = 1;
    let mut product_valid = true;
    
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_result == sum(numbers@.subrange(0, i as int)),
            product_valid ==> product_result == product(numbers@.subrange(0, i as int)),
            product_valid ==> product_result as int == product(numbers@.subrange(0, i as int)),
            product_valid ==> product(numbers@.subrange(0, i as int)) <= u32::MAX,
    {
        let val = numbers[i];
        
        proof {
            sum_fold_left_step(numbers@, i as nat);
        }
        sum_result = sum_result + val as u64;
        
        if product_valid {
            if product_result as u64 * val as u64 <= u32::MAX as u64 {
                proof {
                    product_fold_left_step(numbers@, i as nat);
                }
                product_result = product_result * val;
            } else {
                product_valid = false;
            }
        }
        
        i = i + 1;
    }
    
    proof {
        sum_fold_left_complete(numbers@);
        if product_valid {
            product_fold_left_complete(numbers@);
        }
    }
    
    if product_valid {
        (sum_result, Some(product_result))
    } else {
        (sum_result, None)
    }
}
// </vc-code>

fn main() {}
}