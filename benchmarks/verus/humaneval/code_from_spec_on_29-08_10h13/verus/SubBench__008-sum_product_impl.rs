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
spec fn sum_up_to(numbers: Seq<u32>, i: nat) -> int
    decreases numbers.len() - i
{
    if i >= numbers.len() {
        0
    } else {
        numbers[i as int] + sum_up_to(numbers, i + 1)
    }
}

spec fn product_up_to(numbers: Seq<u32>, i: nat) -> int
    decreases numbers.len() - i
{
    if i >= numbers.len() {
        1
    } else {
        numbers[i as int] * product_up_to(numbers, i + 1)
    }
}

spec fn sum_from_to(numbers: Seq<u32>, start: nat, end: nat) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        numbers[start as int] + sum_from_to(numbers, start + 1, end)
    }
}

spec fn product_from_to(numbers: Seq<u32>, start: nat, end: nat) -> int
    decreases end - start
{
    if start >= end {
        1
    } else {
        numbers[start as int] * product_from_to(numbers, start + 1, end)
    }
}

proof fn sum_equivalence(numbers: Seq<u32>)
    ensures sum(numbers) == sum_up_to(numbers, 0)
{
    assert(sum(numbers) == numbers.fold_left(0, |acc: int, x| acc + x));
    sum_up_to_equiv_fold_left(numbers, 0, 0);
}

proof fn sum_up_to_equiv_fold_left(numbers: Seq<u32>, acc: int, i: nat)
    requires i <= numbers.len()
    ensures acc + sum_up_to(numbers, i) == numbers.subrange(i as int, numbers.len() as int).fold_left(acc, |acc: int, x| acc + x)
    decreases numbers.len() - i
{
    if i >= numbers.len() {
        assert(numbers.subrange(i as int, numbers.len() as int) == Seq::<u32>::empty());
    } else {
        sum_up_to_equiv_fold_left(numbers, acc + numbers[i as int], i + 1);
        assert(numbers.subrange(i as int, numbers.len() as int) == seq![numbers[i as int]].add(numbers.subrange((i + 1) as int, numbers.len() as int)));
    }
}

proof fn product_equivalence(numbers: Seq<u32>)
    ensures product(numbers) == product_up_to(numbers, 0)
{
    assert(product(numbers) == numbers.fold_left(1, |acc: int, x| acc * x));
    product_up_to_equiv_fold_left(numbers, 1, 0);
}

proof fn product_up_to_equiv_fold_left(numbers: Seq<u32>, acc: int, i: nat)
    requires i <= numbers.len()
    ensures acc * product_up_to(numbers, i) == numbers.subrange(i as int, numbers.len() as int).fold_left(acc, |acc: int, x| acc * x)
    decreases numbers.len() - i
{
    if i >= numbers.len() {
        assert(numbers.subrange(i as int, numbers.len() as int) == Seq::<u32>::empty());
    } else {
        product_up_to_equiv_fold_left(numbers, acc * numbers[i as int], i + 1);
        assert(numbers.subrange(i as int, numbers.len() as int) == seq![numbers[i as int]].add(numbers.subrange((i + 1) as int, numbers.len() as int)));
    }
}

proof fn sum_split_lemma(numbers: Seq<u32>, i: nat)
    requires i <= numbers.len()
    ensures sum_up_to(numbers, 0) == sum_from_to(numbers, 0, i) + sum_up_to(numbers, i)
    decreases i
{
    if i == 0 {
        assert(sum_from_to(numbers, 0, 0) == 0);
    } else {
        /* code modified by LLM (iteration 5): cast i - 1 to nat to fix type mismatch */
        sum_split_lemma(numbers, (i - 1) as nat);
    }
}
// </vc-helpers>

// <vc-description>
/*
docstring: Implement sum product.
*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut sum_result: u64 = 0;
    let mut product_result: u64 = 1;
    let mut i = 0;

    proof {
        sum_equivalence(numbers@);
        product_equivalence(numbers@);
    }

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_result == sum_from_to(numbers@, 0, i as nat),
            product_result == product_from_to(numbers@, 0, i as nat) || product_result > u32::MAX,
            product_result <= u64::MAX,
        decreases numbers.len() - i
    {
        sum_result = sum_result + numbers[i] as u64;
        
        if product_result <= u32::MAX as u64 && numbers[i] as u64 <= u32::MAX as u64 / product_result {
            product_result = product_result * numbers[i] as u64;
        } else {
            product_result = u64::MAX;
        }
        
        i = i + 1;
    }

    proof {
        sum_split_lemma(numbers@, numbers.len() as nat);
        assert(sum_result == sum_from_to(numbers@, 0, numbers.len() as nat));
        assert(sum_from_to(numbers@, 0, numbers.len() as nat) == sum_up_to(numbers@, 0));
        assert(sum_up_to(numbers@, 0) == sum(numbers@));
    }

    let final_product = if product_result <= u32::MAX as u64 {
        Some(product_result as u32)
    } else {
        None
    };

    (sum_result, final_product)
}
// </vc-code>

}
fn main() {}