// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn all_remainders_distinct(n: int, k: int) -> bool {
    valid_input(n, k) ==> forall|i: int| 1 <= i <= k ==> #[trigger] (n % i) == (i - 1)
}

spec fn has_non_distinct_remainder(n: int, k: int) -> bool {
    valid_input(n, k) ==> exists|i: int| 1 <= i <= k && #[trigger] (n % i) != (i - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change */
fn check_remainders(n_int: int, k_int: int) -> (result: bool)
    requires
        valid_input(n_int, k_int),
    ensures
        result == all_remainders_distinct(n_int, k_int)
{
    let mut i: int = 1;
    while i <= k_int
        invariant
            1 <= i,
            k_int >= 1,
            valid_input(n_int, k_int),
            forall|j: int| 1 <= j < i ==> (n_int % j) == (j - 1),
        decreases
            k_int - i
    {
        if (n_int % i) != (i - 1) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: String)
    requires
        valid_input(n as int, k as int),
    ensures
        result@ == seq!['Y', 'e', 's', '\n'] <==> all_remainders_distinct(n as int, k as int),
        result@ == seq!['N', 'o', '\n'] <==> has_non_distinct_remainder(n as int, k as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): remove heapstr! and use string literals */
{
    let ghost n_int: int = n as int;
    let ghost k_int: int = k as int;

    if check_remainders(n_int, k_int) {
        String::from("Yes\n")
    } else {
        String::from("No\n")
    }
}
// </vc-code>


}

fn main() {}