// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): step lemma for product_prefix */
proof fn lemma_product_prefix_step(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        product_prefix(a, i + 1) == product_prefix(a, i) * a[i],
{
    if i == 0 {
        assert(product_prefix(a, 1) == a[0]);
        assert(product_prefix(a, 0) == 1);
        assert(product_prefix(a, 1) == product_prefix(a, 0) * a[0]);
    } else {
        assert(i + 1 > 1);
        assert(product_prefix(a, i + 1) == product_prefix(a, i) * a[i]);
    }
}

/* helper modified by LLM (iteration 3): map-index lemma for casting i8 to int */
proof fn lemma_map_index_i8_to_int(a: Seq<i8>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        a.map(|_j, x: i8| x as int)[i] == a[i] as int,
{
    assert(a.map(|_j, x: i8| x as int)[i] == a[i] as int);
}
// </vc-helpers>

// <vc-spec>
spec fn product_prefix(a: Seq<int>, end: int) -> int
    decreases end
{
    if end <= 0 {
        1
    } else if end == 1 {
        a[0]
    } else {
        product_prefix(a, end - 1) * a[end - 1]
    }
}

fn cumprod(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == product_prefix(a@.map(|_index, x: i8| x as int), i + 1),
        forall|i: int, j: int| 0 <= i < a.len() && j == i + 1 && j < a.len() ==> 
            result[j] as int == (result[i] as int) * (a[j] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use seq view in invariants, remove problematic trigger, and reason precisely about push and indices */
    let n = a.len();
    let ghost a_seq: Seq<int> = a@.map(|_index, x: i8| x as int);
    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            r.len() == i,
            i <= n,
            forall|k: int| 0 <= k < r.len() as int ==> (r@[k] as int) == product_prefix(a_seq, k + 1),
        decreases (n as int) - (i as int)
    {
        if i == 0 {
            let next: i8 = a[0];
            let ghost r_before = r@;
            let old_len: usize = r.len();
            r.push(next);
            proof {
                let k: int = i as int;
                assert(k == 0);
                assert(r@ == r_before.push(next));
                assert(k == old_len as int);
                assert(r@[k] == r_before.push(next)[k]);
                assert(r_before.push(next)[k] == next);
                assert(product_prefix(a_seq, 1) == a_seq[0]);
                lemma_map_index_i8_to_int(a@, 0);
                assert(a_seq[0] == a@[0] as int);
                assert(r@[0] as int == product_prefix(a_seq, 1));
            }
        } else {
            let ri1: i8 = r[i - 1];
            let ai: i8 = a[i];
            let next: i8 = ri1 * ai;
            let ghost r_before = r@;
            let old_len: usize = r.len();
            r.push(next);
            proof {
                let k: int = i as int;
                assert(0 <= k - 1);
                assert(r@ == r_before.push(next));
                assert(k == old_len as int);
                // New element after push
                assert(r@[k] == r_before.push(next)[k]);
                assert(r_before.push(next)[k] == next);
                // Previous element unchanged
                assert(k - 1 < r_before.len() as int);
                assert(r@[k - 1] == r_before[k - 1]);
                // Instantiate invariant from the state before push (captured by r_before)
                assert(0 <= k - 1 < r_before.len() as int);
                // From loop invariant at loop head (applied to pre-push r), we know for k-1:
                // r_before[k-1] as int == product_prefix(a_seq, k)
                // Use equal r@[k-1] == r_before[k-1]
                assert(r@[k - 1] as int == product_prefix(a_seq, k));
                // Relate next to previous and current input
                assert(a@[k] == ai);
                assert(r@[k - 1] == ri1);
                assert((next as int) == (ri1 as int) * (ai as int));
                assert((r@[k] as int) == (r@[k - 1] as int) * (a@[k] as int));
                // product_prefix step
                lemma_product_prefix_step(a_seq, k);
                lemma_map_index_i8_to_int(a@, k);
                assert(product_prefix(a_seq, k + 1) == product_prefix(a_seq, k) * a_seq[k]);
                assert(a_seq[k] == a@[k] as int);
                assert(r@[k] as int == product_prefix(a_seq, k + 1));
            }
        }
        i = i + 1;
    }
    proof {
        // Neighbor-step postcondition
        assert forall|i: int, j: int|
            0 <= i < r.len() as int && j == i + 1 && j < r.len() as int
            implies (r@[j] as int) == (r@[i] as int) * (a@[j] as int)
        by
        {
            assert(0 <= j < a.len() as int);
            assert(r@[i] as int == product_prefix(a_seq, i + 1));
            assert(r@[j] as int == product_prefix(a_seq, j + 1));
            lemma_product_prefix_step(a_seq, j);
            assert(product_prefix(a_seq, j + 1) == product_prefix(a_seq, j) * a_seq[j]);
            assert(product_prefix(a_seq, j) == product_prefix(a_seq, i + 1));
            lemma_map_index_i8_to_int(a@, j);
            assert(a_seq[j] == a@[j] as int);
        }
    }
    r
}
// </vc-code>


}
fn main() {}