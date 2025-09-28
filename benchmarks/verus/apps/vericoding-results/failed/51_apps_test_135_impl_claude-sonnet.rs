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
/* helper modified by LLM (iteration 5): fixed trigger issues by using separate specs */
spec fn all_remainders_distinct_equiv(n: int, k: int) -> bool
{
    valid_input(n, k) ==> (forall|i: int| 1 <= i <= k ==> #[trigger] (n % i) == (i - 1))
}

spec fn has_non_distinct_remainder_equiv(n: int, k: int) -> bool
{
    valid_input(n, k) ==> (exists|i: int| 1 <= i <= k && #[trigger] (n % i) != (i - 1))
}

proof fn mutually_exclusive(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        all_remainders_distinct(n, k) <==> !has_non_distinct_remainder(n, k),
{
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
{
    /* code modified by LLM (iteration 5): simplified logic to avoid trigger issues */
    let mut i: i8 = 1;
    while i <= k
        invariant
            1 <= i <= k + 1,
            forall|j: int| 1 <= j < i ==> #[trigger] ((n as int) % j) == j - 1,
        decreases k + 1 - i
    {
        if (n % i) != (i - 1) {
            return "No\n".to_string();
        }
        i = i + 1;
    }
    
    "Yes\n".to_string()
}
// </vc-code>


}

fn main() {}