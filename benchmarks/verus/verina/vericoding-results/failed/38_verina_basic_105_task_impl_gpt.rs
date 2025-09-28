// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix nat/int index in push-last lemma and make postconditions explicit via asserts */
proof fn lemma_seq_push_index_preserved<T>(s: Seq<T>, x: T, j: int)
    requires
        0 <= j < s.len(),
    ensures
        s.push(x)[j] == s[j],
{
    assert(s.push(x).len() == s.len() + 1);
    assert(0 <= j < s.push(x).len());
    assert(s.push(x)[j] == s[j]);
}

proof fn lemma_seq_push_last<T>(s: Seq<T>, x: T)
    ensures
        s.push(x)[s.len() as int] == x,
{
    assert(s.push(x).len() == s.len() + 1);
    assert(s.push(x)[s.len() as int] == x);
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix spec indexing to use int, maintain invariant across push */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> res[j] == a[j] * b[j],
        decreases (a.len() as int) - (i as int)
    {
        let prod: i32 = a[i] * b[i];
        let ghost old_res = res@;
        res.push(prod);
        proof {
            assert(res@ == old_res.push(prod));
            assert(old_res.len() == i as int);
            assert forall|j: int|
                0 <= j && j < i as int + 1 ==> res[j] == a[j] * b[j]
            by {
                if j < i as int {
                    lemma_seq_push_index_preserved(old_res, prod, j);
                    assert(res@[j] == old_res.push(prod)[j]);
                    assert(old_res.push(prod)[j] == old_res[j]);
                    assert(old_res[j] == a[j] * b[j]);
                } else {
                    assert(j == i as int);
                    lemma_seq_push_last(old_res, prod);
                    assert(res@[j] == old_res.push(prod)[j]);
                    assert(res@[j] == prod);
                    assert(prod == a[i as int] * b[i as int]);
                }
            };
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}