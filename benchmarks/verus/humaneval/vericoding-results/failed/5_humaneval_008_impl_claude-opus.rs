// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn product_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        1
    } else {
        s[0] * product_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion for reveal_with_fuel */
proof fn sum_seq_append(s: Seq<int>, x: int)
    ensures sum_seq(s.push(x)) == sum_seq(s) + x
    decreases s.len()
{
    reveal_with_fuel(sum_seq, s.len() + 1);
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(sum_seq(s.push(x)) == x);
        assert(sum_seq(s) == 0);
    } else {
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s.subrange(1, s.len() as int).push(x));
    }
}

proof fn product_seq_append(s: Seq<int>, x: int)
    ensures product_seq(s.push(x)) == product_seq(s) * x
    decreases s.len()
{
    reveal_with_fuel(product_seq, s.len() + 1);
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(product_seq(s.push(x)) == x);
        assert(product_seq(s) == 1);
    } else {
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s.subrange(1, s.len() as int).push(x));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<i8>) -> (result: (i8, i8))
    ensures ({
        let (sum, product) = result;
        sum as int == sum_seq(numbers@.map(|i, x| x as int)) &&
        product as int == product_seq(numbers@.map(|i, x| x as int)) &&
        (numbers@.len() == 0 ==> sum == 0 && product == 1)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed to main code */
    let mut sum: i8 = 0;
    let mut product: i8 = 1;
    let mut i: usize = 0;
    let ghost sum_ghost = numbers@.map(|j, x| x as int);
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum as int == sum_seq(sum_ghost.subrange(0, i as int)),
            product as int == product_seq(sum_ghost.subrange(0, i as int)),
    {
        proof {
            assert(sum_ghost.subrange(0, (i + 1) as int) =~= sum_ghost.subrange(0, i as int).push(sum_ghost[i as int]));
            sum_seq_append(sum_ghost.subrange(0, i as int), sum_ghost[i as int]);
            product_seq_append(sum_ghost.subrange(0, i as int), sum_ghost[i as int]);
        }
        sum = sum + numbers[i];
        product = product * numbers[i];
        i = i + 1;
    }
    
    proof {
        assert(sum_ghost.subrange(0, numbers.len() as int) =~= sum_ghost);
    }
    
    (sum, product)
}
// </vc-code>


}

fn main() {}