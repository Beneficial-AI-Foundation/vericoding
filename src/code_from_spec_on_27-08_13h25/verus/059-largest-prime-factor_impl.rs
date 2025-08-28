use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
fn is_prime(num: u32) -> (result: bool)
    requires
        num >= 2,
    ensures
        result <==> spec_prime(num as int),
{
    let mut i = 2;
    let mut result = true;
    while i < num
        invariant
            2 <= i <= num,
            result <==> spec_prime_helper(num as int, i as int),
        decreases
            num - i,
    {
        if num % i == 0 {
            result = false;
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn largest_prime_factor(n: u32) -> (largest: u32)
    requires
        n >= 2,
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
{
    let mut n = n;
    let mut largest = 1;
    let mut i = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            1 <= largest <= n,
            largest > 1 ==> spec_prime(largest as int),
            forall|k: u32| largest < k <= n ==> !spec_prime(k as int) || k > n / i,
        decreases
            n + 1 - i,
    {
        if n % i == 0 {
            if is_prime(i) {
                largest = i;
            }
            n = n / i;
        } else {
            i = i + 1;
        }
    }
    largest
}
// </vc-code>

}
fn main() {}