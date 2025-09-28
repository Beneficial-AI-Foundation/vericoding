// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): properties of Seq push (length and indexing preservation) */
proof fn lemma_seq_push_props<T>(s: Seq<T>, x: T)
    ensures
        s.push(x).len() == s.len() + 1,
        forall|j: int| 0 <= j < s.len() as int ==> s.push(x)[j] == s[j],
        s.push(x)[s.len() as int] == x,
{
}

// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid exec-mode use of result@; use old(result@) in proof to maintain invariant and show postconditions */
    let len1 = c1.len();
    let len2 = c2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };

    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;

    while i < max_len
        invariant
            result@.len() == i as int,
            i <= max_len,
            forall|j: int| 0 <= j < i as int ==> {
                let v1: int = if j < c1@.len() { c1@[j] as int } else { 0 };
                let v2: int = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == v1 + v2
            },
        decreases max_len as int - i as int
    {
        let a: i8 = if i < len1 { c1[i] } else { 0i8 };
        let b: i8 = if i < len2 { c2[i] } else { 0i8 };
        let s: i8 = a + b;

        result.push(s);

        proof {
            // lengths of inputs match their views
            assert(c1@.len() == len1 as int);
            assert(c2@.len() == len2 as int);

            // characterize the new result view after push
            assert(result@ == old(result@).push(s));
            lemma_seq_push_props::<i8>(old(result@), s);

            // index of the newly appended element
            let idx: int = i as int;
            assert(old(result@).len() as int == idx);
            assert(result@[idx] == s);

            // relate a and b with c1@ and c2@
            let v1i: int = if idx < c1@.len() { c1@[idx] as int } else { 0 };
            let v2i: int = if idx < c2@.len() { c2@[idx] as int } else { 0 };

            if i < len1 {
                assert(idx < c1@.len());
                assert(c1@[idx] == c1[i]);
                assert(a == c1[i]);
                assert(a as int == v1i);
            } else {
                assert(!(idx < c1@.len()));
                assert(v1i == 0);
                assert(a as int == 0);
            }
            if i < len2 {
                assert(idx < c2@.len());
                assert(c2@[idx] == c2[i]);
                assert(b == c2[i]);
                assert(b as int == v2i);
            } else {
                assert(!(idx < c2@.len()));
                assert(v2i == 0);
                assert(b as int == 0);
            }

            assert(result@[idx] as int == v1i + v2i);
        }

        i = i + 1usize;
    }

    result
}

// </vc-code>


}
fn main() {}