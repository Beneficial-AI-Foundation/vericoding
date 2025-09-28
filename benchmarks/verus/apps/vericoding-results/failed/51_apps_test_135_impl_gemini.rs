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
/* helper modified by LLM (iteration 5): [unchanged from previous correct version] */
proof fn lemma_witness_for_has_non_distinct(n: int, k: int, i: int)
    requires
        valid_input(n, k),
        1 <= i <= k,
        (n % i) != (i - 1),
    ensures
        has_non_distinct_remainder(n, k),
{
    assert(has_non_distinct_remainder(n, k)) by {
        assert(exists|j: int| 1 <= j <= k && #[trigger] (n % j) != (j - 1));
    };
}

/* helper modified by LLM (iteration 5): [unchanged from previous correct version] */
proof fn lemma_extend_forall_scope(n: int, i: int)
    requires
        1 <= i,
        forall|j: int| 1 <= j < i ==> #[trigger] (n % j) == (j - 1),
        (n % i) == (i - 1),
    ensures
        forall|j: int| 1 <= j < i + 1 ==> #[trigger] (n % j) == (j - 1),
{
    assert forall|j: int| 1 <= j < i + 1 implies #[trigger] (n % j) == (j - 1) by {
        if j < i {
            assert((n % j) == (j - 1));
        } else {
            assert(j == i);
            assert((n % i) == (i - 1));
        }
    };
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
/* code modified by LLM (iteration 5): [fixed compilation error by correcting the name of the Euclidean division lemma] */
{
    let mut i: i16 = 1;
    while i <= (k as i16)
        invariant
            1 <= i <= (k as i16) + 1,
            valid_input(n as int, k as int),
            forall|j: int| 1 <= j < i as int ==> (n as int % j) == (j - 1),
        decreases (k as i16) - i
    {
        let i_i8 = i as i8;
        let rem = n % i_i8;
        let expected = i_i8 - 1;

        if rem != expected {
            proof {
                vstd::arithmetic::div_mod::lemma_mod_is_euclidean(n as int, i_i8 as int);
                lemma_witness_for_has_non_distinct(n as int, k as int, i as int);
            }
            return "No\n".to_string();
        } else {
            proof {
                vstd::arithmetic::div_mod::lemma_mod_is_euclidean(n as int, i_i8 as int);
                lemma_extend_forall_scope(n as int, i as int);
            }
        }
        i = i + 1;
    }

    proof {
        assert(all_remainders_distinct(n as int, k as int));
    }
    return "Yes\n".to_string();
}
// </vc-code>


}

fn main() {}