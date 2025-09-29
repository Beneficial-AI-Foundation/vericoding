// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<int>) -> bool 
    decreases a.len()
{
    false  /* integers can't be NaN */
}

spec fn has_non_nan(a: Seq<int>) -> bool 
    decreases a.len()
{
    a.len() > 0  /* all integers are non-NaN */
}

spec fn is_min_of_all(result: int, a: Seq<int>) -> bool {
    exists|witness: int| 0 <= witness < a.len() &&
        result == a[witness] &&
        forall|j: int| 0 <= j < a.len() ==> result <= a[j]
}

fn nanmin(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures is_min_of_all(result as int, a@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [added proof block to connect loop invariants to postcondition] */
    let mut min_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < (i as int) && min_val == a@[k],
            forall|j: int| 0 <= j < (i as int) ==> min_val as int <= a@[j] as int,
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i = i + 1;
    }

    proof {
        let a_int = a@.map(|_i, x: i8| x as int);

        assert forall|j: int| 0 <= j < a.len() implies min_val as int <= a_int[j] by { }

        let witness = choose |k: int| 0 <= k < (a.len() as int) && min_val == a@[k];
        assert(min_val as int == a_int[witness]);

        assert(is_min_of_all(min_val as int, a_int));
    }

    min_val
}
// </vc-code>


}
fn main() {}