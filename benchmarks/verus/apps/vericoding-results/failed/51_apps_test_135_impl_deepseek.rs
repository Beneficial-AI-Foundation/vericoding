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
/* helper modified by LLM (iteration 5): Added #[trigger] annotations to fix quantifier errors */
proof fn lemma_all_remainders_distinct_iff(n: int, k: int) 
    requires valid_input(n, k),
    ensures all_remainders_distinct(n, k) == forall|i: int| 1 <= i <= k ==> #[trigger] (n % i) == i - 1,
{
}

proof fn lemma_distinct_remainders_imply_no(n: int, k: int) 
    requires valid_input(n, k),
    ensures has_non_distinct_remainder(n, k) == (exists|i: int| 1 <= i <= k && #[trigger] (n % i) != i - 1),
{
}

proof fn lemma_inductive_step(n: int, k: int, i: int)
    requires 
        valid_input(n, k),
        1 <= i <= k,
    ensures 
        (forall|j: int| 1 <= j < i ==> #[trigger] (n % j) == j - 1) && #[trigger] (n % i) == i - 1 ==> 
        forall|j: int| 1 <= j <= i ==> #[trigger] (n % j) == j - 1,
{
    if (forall|j: int| 1 <= j < i ==> #[trigger] (n % j) == j - 1) && #[trigger] (n % i) == i - 1 {
        assert forall|j: int| 1 <= j <= i implies #[trigger] (n % j) == j - 1 by {
            if j < i {
                assert(#[trigger] (n % j) == j - 1);
            } else {
                assert(j == i);
                assert(#[trigger] (n % i) == i - 1);
            }
        };
    }
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
    /* code modified by LLM (iteration 5): Fixed loop invariant with #[trigger] annotations */
    proof {
        lemma_all_remainders_distinct_iff(n as int, k as int);
        lemma_distinct_remainders_imply_no(n as int, k as int);
    }
    
    let mut i: i8 = 1;
    
    while i <= k
        invariant
            1 <= i <= k + 1,
            forall|j: int| 1 <= j < i as int ==> #[trigger] ((n as int) % j) == j - 1,
        decreases (k as int) - (i as int),
    {
        let remainder = n % i;
        let expected = i - 1;
        
        if remainder != expected {
            return "No\n".to_string();
        }
        
        proof {
            lemma_inductive_step(n as int, k as int, i as int);
        }
        
        i = i + 1;
    }
    
    "Yes\n".to_string()
}
// </vc-code>


}

fn main() {}