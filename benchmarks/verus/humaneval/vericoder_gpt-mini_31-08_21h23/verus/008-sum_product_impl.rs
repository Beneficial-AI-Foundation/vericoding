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
// helper lemmas for bounding sums and products

spec fn prefix_sum(numbers: Seq<u32>, i: nat) -> int {
    if i == 0 {
        0
    } else {
        prefix_sum(numbers, i - 1) + (numbers@[i - 1] as int)
    }
}

proof fn prefix_sum_eq_sum_aux(numbers: Seq<u32>, i: nat)
    decreases i
    ensures prefix_sum(numbers, i) == numbers[..i].fold_left(0, |acc: int, x| acc + x)
{
    if i == 0 {
        // prefix_sum(...,0) == 0 == fold_left over empty prefix
    } else {
        prefix_sum_eq_sum_aux(numbers, i - 1);
        // By definition of prefix_sum
        assert(prefix_sum(numbers, i) == prefix_sum(numbers, i - 1) + (numbers@[i - 1] as int));
        // By definition of fold_left on the prefix
        assert(numbers[..i].fold_left(0, |acc: int, x| acc + x) ==
               numbers[..i - 1].fold_left(0, |acc: int, x| acc + x) + (numbers@[i - 1] as int));
        // Use induction hypothesis
        assert(prefix_sum(numbers, i - 1) == numbers[..i - 1].fold_left(0, |acc: int, x| acc + x));
        // Conclude equality for i
    }
}

proof fn prefix_sum_eq_sum(numbers: Seq<u32>)
    ensures prefix_sum(numbers, numbers.len()) == sum(numbers)
{
    prefix_sum_eq_sum_aux(numbers, numbers.len());
    // sum(numbers) is numbers.fold_left over full sequence
    assert(prefix_sum(numbers, numbers.len()) == numbers[..numbers.len()].fold_left(0, |acc: int, x| acc + x));
    assert(numbers[..numbers.len()].fold_left(0, |acc: int, x| acc + x) == sum(numbers));
}

proof fn prefix_sum_bound(numbers: Seq<u32>, i: nat)
    decreases i
    requires i <= numbers.len()
    ensures prefix_sum(numbers, i) <= (i as int) * (u32::MAX as int)
{
    if i == 0 {
        // 0 <= 0
    } else {
        prefix_sum_bound(numbers, i - 1);
        // numbers@[i-1] as int <= u32::MAX as int
        assert((numbers@[i - 1] as int) <= (u32::MAX as int));
        assert(prefix_sum(numbers, i) == prefix_sum(numbers, i - 1) + (numbers@[i - 1] as int));
        assert(prefix_sum(numbers, i) <= ((i - 1) as int) * (u32::MAX as int) + (u32::MAX as int));
        assert(((i - 1) as int) * (u32::MAX as int) + (u32::MAX as int) == (i as int) * (u32::MAX as int));
    }
}

proof fn u32sq_minus_lt_u64()
    ensures ((u32::MAX as int - 1) * (u32::MAX as int)) < (u64::MAX as int)
{
    let a: int = u32::MAX as int;
    let lhs: int = (a - 1) * a;
    let rhs: int = u64::MAX as int;
    assert(lhs == a * a - a);
    assert(lhs < rhs);
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
    let mut sum64: u64 = 0;
    let mut i: usize = 0;
    let n = numbers.len();
    let mut ghost s: int = 0;

    while i < n
        invariant
            i <= n,
            sum64 as int == s,
            s == prefix_sum(numbers@, i),
            s <= (i as int) * (u32::MAX as int),
    {
        let x: u32 = numbers[i];
        sum64 = sum64 + (x as u64);
        ghost { s = s + (x as int); }
        i += 1;
    }

    // After loop, invariants give the relationships we need
    ghost {
        assert(sum64 as int == s);
        assert(s == prefix_sum(numbers@, n));
    }
    prefix_sum_eq_sum(numbers@);
    ghost {
        assert(sum64 as int
// </vc-code>

fn main() {}
}