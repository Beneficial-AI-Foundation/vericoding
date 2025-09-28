// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma that zeros in range make product zero */
proof fn prod_helper_zero_lemma(a: Seq<i32>, start: int, finish: int)
    requires
        0 <= start,
        start <= finish,
        finish <= a.len() as int,
    ensures
        forall|i: int| start <= i < finish && a@[i] == 0 ==> prod_spec_helper(a, start, finish) == 0,
    decreases finish - start
{
    if start >= finish {
        // empty range: vacuously true
    } else {
        if a@[start] == 0 {
            proof {
                assert(prod_spec_helper(a, start, finish) == a@[start] * prod_spec_helper(a, start + 1, finish));
                assert(a@[start] * prod_spec_helper(a, start + 1, finish) == 0);
            }
        } else {
            prod_helper_zero_lemma(a, start + 1, finish);
            proof {
                assert(prod_spec_helper(a, start, finish) == a@[start] * prod_spec_helper(a, start + 1, finish));
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
spec fn prod_spec_helper(a: Seq<i32>, start: int, finish: int) -> int
    decreases finish - start
{
    if start >= finish {
        1
    } else {
        a[start] * prod_spec_helper(a, start + 1, finish)
    }
}

spec fn prod_spec(a: Seq<i32>) -> int {
    prod_spec_helper(a, 0, a.len() as int)
}

spec fn prod_array_spec(a: Seq<i32>, start: int, finish: int) -> int {
    prod_spec_helper(a, start, finish)
}

fn prod(a: Vec<i32>) -> (result: i32)
    ensures result == prod_spec(a@)
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn prod_array(a: Vec<i32>, start: usize, finish: usize) -> (result: i32)
    requires 
        start <= finish,
        finish <= a.len(),
    ensures result == prod_array_spec(a@, start as int, finish as int)
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn prod_theorem(a: Vec<i32>)
    requires a.len() > 0,
    ensures 
        prod_spec(a@) == prod_array_spec(a@, 0, a.len() as int) &&
        (forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> prod_spec(a@) == 0)
{
    assume(false);
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): delegate to prod_array over full range */
    result = prod_array(a, 0, a.len());
}

{
    /* code modified by LLM (iteration 3): iterative product over [start, finish) */
    let mut i: usize = start;
    let mut res: i32 = 1;
    while i < finish
        invariant
            start <= i <= finish,
            res == prod_spec_helper(a@, start as int, i as int),
        decreases finish - i
    {
        let ai: i32 = a[i];
        res = res * ai;
        i = i + 1;
    }
    result = res;
}

{
    /* code modified by LLM (iteration 3): prove prod_spec equals prod_array_spec and zeros imply zero product */
    proof {
        // prod_spec is defined via prod_spec_helper
        assert(prod_spec(a@) == prod_spec_helper(a@, 0, a.len() as int));
        assert(prod_array_spec(a@, 0, a.len() as int) == prod_spec_helper(a@, 0, a.len() as int));
    }
    prod_helper_zero_lemma(a@, 0, a.len() as int);
    proof {
        // From lemma, for any i in range, if a@[i] == 0 then product is zero
        assert(forall|i: int| 0 <= i < a.len() as int && a@[i] == 0 ==> prod_spec_helper(a@, 0, a.len() as int) == 0);
    }
}

// </vc-code>


}
fn main() {}