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
{
    let mut temp = n;
    let mut largest = 1;
    let mut i = 2;
    while i <= temp / i {
        if temp % i == 0 {
            largest = i;
            while temp % i == 0 {
                temp /= i;
            } invariant (n % temp == 0 && temp % i == 0);
        }
        i += 1;
    } invariant (n % temp == 0 && (largest == 1 || largest < i) && 2 <= i);
    if temp > 1 {
        largest = temp;
    }
    largest
}
// </vc-code>

fn main() {}
}