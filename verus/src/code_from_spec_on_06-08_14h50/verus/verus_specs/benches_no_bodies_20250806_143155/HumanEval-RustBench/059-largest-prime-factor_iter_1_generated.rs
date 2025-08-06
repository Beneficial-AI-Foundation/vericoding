use vstd::prelude::*;

verus! {
spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

fn is_prime(num: u32) -> (result: bool)
    // pre-conditions-start
    requires
        num >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> spec_prime(num as int),
    // post-conditions-end
{
    let mut i = 2;
    while i * i <= num
        invariant
            2 <= i <= num + 1,
            forall|j: int| 2 <= j < i ==> (#[trigger] ((num as int) % j)) != 0,
    {
        if num % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}

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
{
    let mut num = n;
    let mut largest_factor = 2;
    let mut i = 2;
    
    while i * i <= num
        invariant
            2 <= i,
            2 <= num <= n,
            2 <= largest_factor <= n,
            spec_prime(largest_factor as int),
            (n as int) % (num as int) == 0,
    {
        while num % i == 0
            invariant
                2 <= i,
                2 <= num <= n,
                2 <= largest_factor <= n,
                spec_prime(largest_factor as int),
                (n as int) % (num as int) == 0,
        {
            if is_prime(i) {
                largest_factor = i;
            }
            num = num / i;
        }
        i = i + 1;
    }
    
    if num > 1 {
        largest_factor = num;
    }
    
    largest_factor
}

}
fn main() {}