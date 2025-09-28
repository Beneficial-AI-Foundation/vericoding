// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): instantiate non-zero vector definition to derive element non-zeroness at a given index */
proof fn lemma_non_zero_index(v: Seq<i32>, i: int)
    requires
        is_non_zero_vector(v),
        0 <= i < v.len(),
    ensures
        v[i] != 0,
{
    assert(is_non_zero_vector(v) == forall|j: int| 0 <= j < v.len() ==> v[j] != 0);
    assert(forall|j: int| 0 <= j < v.len() ==> v[j] != 0);
    assert(v[i] != 0);
}

/* helper modified by LLM (iteration 5): relate mapped non-zero property back to the original sequence element */
proof fn lemma_mapped_non_zero_index(v: Seq<i8>, i: int)
    requires
        is_non_zero_vector(v.map(|j, x: i8| x as i32)),
        0 <= i < v.len(),
    ensures
        (v[i] as i32) != 0,
{
    lemma_non_zero_index(v.map(|j, x: i8| x as i32), i);
    assert(v.map(|j, x: i8| x as i32)[i] == v[i] as i32);
    assert((v[i] as i32) != 0);
}

/* helper modified by LLM (iteration 5): from non-zero cast conclude original value is non-zero */
proof fn lemma_cast_nonzero_implies_nonzero(z: i8)
    ensures
        (z as i32) != 0 ==> z != 0,
{
    if z == 0 {
        assert((z as i32) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_non_zero_vector(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn floor_divide(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        is_non_zero_vector(a@.map(|i, x: i8| x as i32)),
        is_non_zero_vector(b@.map(|i, x: i8| x as i32)),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == (a[i] as i32) / (b[i] as i32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix chained inequality assertions and explicitly derive divisor non-zero */
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let ghost mut g: Seq<i8> = Seq::empty();
    while i < n
        invariant
            result.len() == i,
            0 <= i as int,
            i as int <= n as int,
            n == a.len(),
            a.len() == b.len(),
            g.len() as int == i as int,
            g.len() as int <= a.len() as int,
            result@ == g,
            forall|k: int|
                0 <= k < g.len() ==> (g[k] as i32) == (a@[k] as i32) / (b@[k] as i32),
        decreases n as int - i as int
    {
        proof {
            assert(i < n);
            assert(n == a.len());
            assert(a.len() == b.len());
            assert(i < a.len());
            assert(i < b.len());
            assert(0 <= i as int);
            assert(i as int < a.len() as int);
            assert(0 <= i as int);
            assert(i as int < b.len() as int);
        }
        let x: i8 = a[i];
        let y: i8 = b[i];
        proof {
            assert(a@[i as int] == x);
            assert(b@[i as int] == y);
            lemma_mapped_non_zero_index(b@, i as int);
            assert((b@[i as int] as i32) != 0);
            assert((y as i32) == (b@[i as int] as i32));
            assert((y as i32) != 0);
            lemma_cast_nonzero_implies_nonzero(y);
            assert(y != 0);
        }
        let q: i8 = x / y;
        proof {
            let old_len: int = g.len() as int;
            assert(old_len == i as int);
            assert(a@[old_len] == x);
            assert(b@[old_len] == y);
            g = g.push(q);
            assert(g[old_len] == q);
            assert((g[old_len] as i32) == (a@[old_len] as i32) / (b@[old_len] as i32));
        }
        result.push(q);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}