// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): product over a singleton interval equals that element */
proof fn lemma_prod_singleton(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len() as int,
    ensures
        prod_spec_helper(a, i, i + 1) == a[i] as int,
{
    assert(i < i + 1);
    assert(prod_spec_helper(a, i, i + 1) == (a[i] as int) * prod_spec_helper(a, i + 1, i + 1));
    assert(prod_spec_helper(a, i + 1, i + 1) == 1);
    assert(prod_spec_helper(a, i, i + 1) == a[i] as int);
}

/* helper modified by LLM (iteration 5): concatenation property of product over adjacent intervals */
proof fn lemma_prod_concat(a: Seq<i32>, start: int, mid: int, finish: int)
    requires
        0 <= start <= mid <= finish <= a.len() as int,
    ensures
        prod_spec_helper(a, start, finish)
        == prod_spec_helper(a, start, mid) * prod_spec_helper(a, mid, finish),
    decreases finish - start,
{
    if start == finish {
        assert(mid == start);
        assert(prod_spec_helper(a, start, finish) == 1);
        assert(prod_spec_helper(a, start, mid) == 1);
        assert(prod_spec_helper(a, mid, finish) == 1);
    } else if start == mid {
        assert(prod_spec_helper(a, start, mid) == 1);
    } else {
        assert(start < mid);
        assert(start < finish);
        assert(prod_spec_helper(a, start, finish)
            == (a[start] as int) * prod_spec_helper(a, start + 1, finish));
        assert(start + 1 <= mid);
        lemma_prod_concat(a, start + 1, mid, finish);
        assert(prod_spec_helper(a, start + 1, finish)
            == prod_spec_helper(a, start + 1, mid) * prod_spec_helper(a, mid, finish));
        assert(prod_spec_helper(a, start, mid) == (a[start] as int) * prod_spec_helper(a, start + 1, mid));
        assert((a[start] as int) * (prod_spec_helper(a, start + 1, mid) * prod_spec_helper(a, mid, finish))
            == ((a[start] as int) * prod_spec_helper(a, start + 1, mid)) * prod_spec_helper(a, mid, finish));
    }
}

/* helper modified by LLM (iteration 5): if any element in the range is zero, the product over the range is zero */
proof fn lemma_prod_zero_at(a: Seq<i32>, start: int, finish: int, k: int)
    requires
        0 <= start <= k,
        k < finish <= a.len() as int,
    ensures
        a[k] == 0 ==> prod_spec_helper(a, start, finish) == 0,
{
    if a[k] == 0 {
        lemma_prod_concat(a, k, k + 1, finish);
        lemma_prod_singleton(a, k);
        assert(prod_spec_helper(a, k, k + 1) == a[k] as int);
        assert(a[k] as int == 0);
        assert(prod_spec_helper(a, k, finish)
            == prod_spec_helper(a, k, k + 1) * prod_spec_helper(a, k + 1, finish));
        assert(prod_spec_helper(a, k, finish) == 0);
        lemma_prod_concat(a, start, k, finish);
        assert(prod_spec_helper(a, start, finish)
            == prod_spec_helper(a, start, k) * prod_spec_helper(a, k, finish));
        assert(prod_spec_helper(a, start, finish) == 0);
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
    /* code modified by LLM (iteration 5): delegate to prod_array and connect specs */
    proof {
        assert(prod_array_spec(a@, 0, a.len() as int) == prod_spec(a@));
    }
    let r = prod_array(a, 0, a.len());
    r
}

{
    /* code modified by LLM (iteration 5): iterative product with invariant connecting to spec helper */
    let mut i: usize = start;
    let mut acc: i32 = 1;
    while i < finish
        invariant
            start <= i,
            i <= finish,
            acc as int == prod_spec_helper(a@, start as int, i as int),
        decreases (finish as int) - (i as int)
    {
        let ai = a[i];
        proof {
            assert(0 <= start as int);
            assert(start as int <= i as int);
            assert(i as int < finish as int);
            assert(finish as int <= a.len() as int);
            assert(i as int < a.len() as int);
            assert((i + 1) as int <= a.len() as int);
            lemma_prod_concat(a@, start as int, i as int, (i + 1) as int);
            lemma_prod_singleton(a@, i as int);
            assert(prod_spec_helper(a@, i as int, (i + 1) as int) == a@[i as int] as int);
            assert(a@[i as int] == ai);
            assert(prod_spec_helper(a@, start as int, (i + 1) as int)
                == prod_spec_helper(a@, start as int, i as int) * prod_spec_helper(a@, i as int, (i + 1) as int));
            assert(prod_spec_helper(a@, start as int, (i + 1) as int)
                == (acc as int) * (ai as int));
        }
        acc = acc * ai;
        i = i + 1;
    }
    proof {
        assert(acc as int == prod_array_spec(a@, start as int, finish as int));
    }
    acc
}
// </vc-code>


}
fn main() {}