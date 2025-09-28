// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): insertion into a sorted sequence */
fn insert_sorted(x: i8, s: Seq<i8>) -> Seq<i8>
    ensures
        forall|i: int, j: int| 0 <= i < j && j < result.len() ==> result@[i] <= result@[j],
        result.to_multiset() == s.to_multiset().insert(x),
    decreases s.len()
{
    if s.len() == 0 {
        seq![x]
    } else {
        if x <= s@[0] {
            seq![x] + s
        } else {
            let tail = insert_sorted(x, s[1..]);
            seq![s@[0]] + tail
        }
    }
}

/* helper modified by LLM (iteration 5): insertion sort using insert_sorted */
fn insertion_sort(s: Seq<i8>) -> Seq<i8>
    ensures
        forall|i: int, j: int| 0 <= i < j && j < result.len() ==> result@[i] <= result@[j],
        result.to_multiset() == s.to_multiset(),
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else {
        let sorted_tail = insertion_sort(s[1..]);
        insert_sorted(s@[0], sorted_tail)
    }
}
// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): sort elements at even indices while preserving odd indices */
    let n = a@.len();
    let mut evens: Seq<i8> = Seq::empty();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            evens.len() == (i + 1) / 2,
        decreases n - i
    {
        if i % 2 == 0 {
            evens = evens + seq![a@[i]];
        }
        i += 1;
    }

    // After loop, evens contains all elements from even indices
    assert(evens.len() == (n + 1) / 2);

    let sorted_evens = insertion_sort(evens);

    // Reconstruct result Vec with odd indices preserved and even indices from sorted_evens
    let mut res: Vec<i8> = Vec::new();
    let mut k: int = 0;
    while k < n
        invariant
            0 <= k <= n,
            res@.len() == k,
            sorted_evens.len() == (n + 1) / 2,
        decreases n - k
    {
        if k % 2 == 1 {
            res.push(a@[k]);
        } else {
            let eidx = k / 2;
            res.push(sorted_evens@[eidx]);
        }
        k += 1;
    }

    res
}
// </vc-code>


}

fn main() {}