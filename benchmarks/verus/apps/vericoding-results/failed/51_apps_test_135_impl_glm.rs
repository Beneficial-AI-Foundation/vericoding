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
/* helper modified by LLM (iteration 2): lemma to relate exec loop to spec */
proof fn loop_lemma(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        (forall|i: int| 1<=i<=k ==> n % i == i-1) <==> !has_non_distinct_remainder(n, k)
{
    // By definition of has_non_distinct_remainder, we have:
    //   has_non_distinct_remainder(n, k) == exists|i: int| 1<=i<=k && n%i != i-1
    // The negation is: !has_non_distinct_remainder(n, k) == forall|i: int| 1<=i<=k ==> n%i == i-1
    // So the lemma is trivial.
    assert(has_non_distinct_remainder(n, k) == !(forall|i: int| 1<=i<=k ==> n%i == i-1));
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
/* code modified by LLM (iteration 5): avoid String::from by using String::new and push */
{
    let mut i: i8 = 1;
    let mut found: bool = false;
    while i <= k {
        if n % i != i - 1 {
            found = true;
        }
        i = i + 1;
    }
    let mut result = String::new();
    if found {
        result.push('N');
        result.push('o');
        result.push('\n');
    } else {
        result.push('Y');
        result.push('e');
        result.push('s');
        result.push('\n');
    }
    proof {
        loop_lemma(n as int, k as int);
        assert(found == has_non_distinct_remainder(n as int, k as int));
    }
    result
}
// </vc-code>


}

fn main() {}