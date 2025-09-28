// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive specification to count occurrences in a Seq of i8 */
spec fn count_rec(a: Seq<i8>, x: i8) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len()), x) + (if a@[0] == x { 1int } else { 0int })
    }
}

/* helper modified by LLM (iteration 5): lemma relating count on a prefix of length j to prefix of length j-1 */
fn count_rec_prefix_lemma(a: Seq<i8>, j: int, x: i8)
    requires
        0 <= j && j <= a.len(),
    ensures
        count_rec(a.subrange(0, j), x) == if j == 0 { 0int } else { count_rec(a.subrange(0, j - 1), x) + (if a@[j - 1] == x { 1int } else { 0int }) },
    decreases a.len() - j
{
    proof {
        if j == 0 {
            // trivial
        } else {
            count_rec_prefix_lemma(a, j - 1, x);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < a@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) >= 1
    ensures 
        forall|i: int| 0 <= i < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[i] as int) == 1,
        forall|i: int| 0 <= i < a@.len() ==> (result@.map(|_i: int, x: i8| x as int).contains(a@[i] as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) == 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate, count occurrences with inner loop, and build result keeping elements with count == 1 */
    let mut res: Vec<i8> = Vec::new();
    let n = a.len();
    let mut i: usize = 0usize;

    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            forall|j: int| 0 <= j && j < i as int ==> (res@.contains(a@[j]) <==> count_rec(a@, a@[j]) == 1),
            forall|k: int| 0 <= k && k < res@.len() ==> exists|j: int| 0 <= j && j < i as int && res@[k] == a@[j],
        decreases (n as int) - (i as int)
    {
        let ai: i8 = a[i].clone();
        let mut cnt: usize = 0usize;
        let mut j: usize = 0usize;

        while j < n
            invariant
                0 <= j as int && j as int <= n as int,
                cnt as int == count_rec(a@.subrange(0, j as int), ai),
            decreases (n as int) - (j as int)
        {
            if a[j] == ai {
                cnt += 1;
            }
            proof {
                count_rec_prefix_lemma(a@, (j as int) + 1int, ai);
                if a@[j as int] == ai {
                    assert(cnt as int == count_rec(a@.subrange(0, j as int), ai) + 1int);
                } else {
                    assert(cnt as int == count_rec(a@.subrange(0, j as int), ai));
                }
                assert(cnt as int == count_rec(a@.subrange(0, (j as int) + 1int), ai));
            }

            j += 1;
        }

        if cnt == 1usize {
            if !res.contains(&ai) {
                res.push(ai);
            }
        }

        i += 1;
    }

    res
}

// </vc-code>


}

fn main() {}