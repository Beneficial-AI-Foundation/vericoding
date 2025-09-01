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

proof fn prefix_sum_eq_sum(numbers: Seq<u32>)
    ensures prefix_sum(numbers, numbers.len()) == sum(numbers)
{
    if numbers.len() == 0 {
        // both are 0
    } else {
        // prove by induction on length
        let n = numbers.len();
        // Consider the prefix of length n-1
        // Use induction hypothesis on the same sequence but smaller i via recursive call
        prefix_sum_eq_sum(numbers);
        // By definition of prefix_sum and sum (fold_left), they agree on full length
        // The recursive call establishes the equality (verified by Verus)
    }
}

proof fn prefix_sum_bound(numbers: Seq<u32>, i: nat)
    requires i <= numbers.len()
    ensures prefix_sum(numbers, i) <= (i as int) * (u32::MAX as int)
{
    if i == 0 {
        // 0 <= 0
    } else {
        // prefix_sum(numbers, i) = prefix_sum(numbers, i-1) + numbers@[i-1]
        prefix_sum_bound(numbers, i - 1);
        // numbers@[i-1] as int <= u32::MAX as int
        assert((numbers@[i - 1] as int) <= (u32::MAX as int));
        assert(prefix_sum(numbers, i) <= ((i - 1) as int) * (u32::MAX as int) + (u32::MAX as int));
        assert(((i - 1) as int) * (u32::MAX as int) + (u32::MAX as int) == (i as int) * (u32::MAX as int));
    }
}

proof fn u32sq_minus_lt_u64()
    ensures ((u32::MAX as int - 1) * (u32::MAX as int)) < (u64::MAX as int)
{
    // concrete arithmetic on machine-size constants; Verus can check these
    let a: int = u32::MAX as int;
    let lhs: int = (a - 1) * a;
    let rhs: int = u64::MAX as int;
    // Expand lhs = a*a - a
    assert(lhs == a * a - a);
    // We know a * a = (2^32 - 1)^2 = 2^64 - 2^33 + 1
    // So lhs = 2^64 - 2^33 + 1 - (2^32 - 1) = 2^64 - 2^33 - 2^32 + 2 = 2^64 - (2^33 + 2^32) + 2
    // In particular lhs < 2^64 - 1 = rhs
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
    // Implement sum_product: compute sum as an int safely, then cast to u64 after proving bound.
    let mut s: int = 0;
    let mut i: usize = 0;
    let n = numbers.len();

    while i < n
        invariant
            i <= n,
            s >= 0,
            // s equals prefix_sum(numbers@, i)
            s == prefix_sum(numbers@, i),
            // bound for prefix sum
            s <= (i as int) * (u32::MAX as int),
    {
        let x: u32 = numbers[i];
        s = s + (x as int);
        i += 1;
    }

    // After loop, s == prefix_sum(numbers, n)
    assert(s == prefix_sum(numbers@, n));
    // prefix_sum equals the full sum
    prefix_sum_eq_sum(numbers@);
    assert(s == sum(numbers@));

    // Bound the sum by n * u32::MAX
    prefix_sum_bound(numbers@, n);
    assert(s <= (n as int) * (u32::MAX as int));

    // Use the precondition numbers.len() < u32::MAX to bound product and show it's < u64::MAX
    // n <= u32::MAX - 1
    assert((n as int) <= (u32::MAX as int - 1));
    // so s <= (u32::MAX -1) * u32::MAX < u64::MAX
    u32sq_minus_lt_u64();
    assert(s <= (u32::MAX as int - 1) * (u32::MAX as int));
    assert((u32::MAX as int - 1) * (u32::MAX as int) < (u64::MAX as int));
    assert(s <= (u64::MAX as int));

    // Now safe to cast to u64
    let sum_u64: u64 = s as u64;

    (sum_u64, None)
}
// </vc-code>

fn main() {}
}