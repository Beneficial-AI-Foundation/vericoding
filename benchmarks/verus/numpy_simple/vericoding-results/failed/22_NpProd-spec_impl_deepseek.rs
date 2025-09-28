// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn prod_helper_lemma(a: Seq<i32>, start: int, finish: int)
    requires
        start <= finish,
    ensures
        prod_spec_helper(a, start, finish) == prod_array_spec(a, start, finish),
    decreases finish - start
{
    if start < finish {
        assert(prod_spec_helper(a, start, finish) == a[start] * prod_spec_helper(a, start + 1, finish));
        assert(prod_array_spec(a, start, finish) == a[start] * prod_array_spec(a, start + 1, finish));
        prod_helper_lemma(a, start + 1, finish);
    } else {
        assert(prod_spec_helper(a, start, finish) == 1);
        assert(prod_array_spec(a, start, finish) == 1);
    }
}

proof fn prod_zero_lemma(a: Seq<i32>, i: int, len: int)
    requires
        i >= 0,
        len >= i,
        a.len() as int >= len,
        a[i] == 0,
    ensures
        prod_spec_helper(a, i, len) == 0,
    decreases len - i
{
    if i < len {
        prod_zero_lemma(a, i + 1, len);
    }
}

proof fn prod_zero_lemma_main(a: Seq<i32>, len: int)
    requires
        len > 0,
    ensures
        forall|i: int| 0 <= i < len && a[i] == 0 ==> prod_spec_helper(a, 0, len) == 0
    decreases len
{
    if len == 1 {
        assert forall|i: int| 0 <= i < 1 && a[i] == 0 implies prod_spec_helper(a, 0, 1) == 0 {
            if a[0] == 0 {
                assert(prod_spec_helper(a, 0, 1) == 0);
            }
        };
    } else {
        prod_zero_lemma_main(a.subrange(0, len - 1), len - 1);
        assert forall|i: int| 0 <= i < len && a[i] == 0 implies prod_spec_helper(a, 0, len) == 0 {
            if i == len - 1 {
                prod_zero_lemma(a, i, len);
                assert(prod_spec_helper(a, 0, len) == prod_spec_helper(a, 0, i) * prod_spec_helper(a, i, len));
                assert(prod_spec_helper(a, i, len) == 0);
                assert(prod_spec_helper(a, 0, len) == 0);
            } else {
                assert(0 <= i < len - 1);
                assert(a.subrange(0, len - 1)@[i] == a[i]);
                assert(prod_spec_helper(a, 0, len) == prod_spec_helper(a, 0, len - 1) * a[len - 1]);
                assert(prod_spec_helper(a, 0, len - 1) == 0);
                assert(prod_spec_helper(a, 0, len) == 0);
            }
        };
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
    /* code modified by LLM (iteration 5): fixed prod_array function body */
    if start == finish {
        1
    } else {
        let mut result: i32 = 1;
        let mut i: usize = start;
        
        while i < finish
            invariant
                start <= i <= finish,
                result == prod_array_spec(a@, start as int, i as int),
            decreases finish - i
        {
            result = result * a[i];
            i = i + 1;
        }
        
        result
    }
}

{
    /* code modified by LLM (iteration 5): fixed prod function body */
    prod_array(a, 0, a.len())
}

{
    /* code modified by LLM (iteration 5): fixed prod_theorem proof body with proper lemmas */
    prod_helper_lemma(a@, 0, a.len() as int);
    prod_zero_lemma_main(a@, a.len() as int);
    assert forall|i: int| 0 <= i < a.len() && a[i] == 0 implies prod_spec(a@) == 0 {
        assert(prod_spec(a@) == prod_spec_helper(a@, 0, a.len() as int));
    };
}
// </vc-code>


}
fn main() {}