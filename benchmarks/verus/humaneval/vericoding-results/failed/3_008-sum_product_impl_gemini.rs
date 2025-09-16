// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_distributes(s: Seq<u32>, x: u32)
    ensures sum(s.push(x)) == sum(s) + (x as int),
{
    reveal(sum);
}

proof fn lemma_product_distributes(s: Seq<u32>, x: u32)
    ensures product(s.push(x)) == product(s) * (x as int),
{
    reveal(product);
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))

    requires
        numbers.len() < u32::MAX,

    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
// </vc-spec>
// <vc-code>
{
    let mut s: u64 = 0;
    let mut p_opt: Option<u32> = Some(1);
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            numbers.len() < u32::MAX,
            s as int == sum(numbers@.subrange(0, i)),
            p_opt.is_Some() ==> p_opt.get_Some_0() as int == product(numbers@.subrange(0, i)),
        decreases numbers.len() - i
    {
        let x = numbers[i];
        
        proof {
            let sub = numbers@.subrange(0, i);
            vstd::seq::lemma_subrange_succ(numbers@, i);
            lemma_sum_distributes(sub, x);
            lemma_product_distributes(sub, x);
        }
        
        s = s + (x as u64);

        if let Some(p_val) = p_opt {
            p_opt = p_val.checked_mul(x);
        }
        
        i = i + 1;
    }
    
    (s,p_opt)
}
// </vc-code>

}
fn main() {}