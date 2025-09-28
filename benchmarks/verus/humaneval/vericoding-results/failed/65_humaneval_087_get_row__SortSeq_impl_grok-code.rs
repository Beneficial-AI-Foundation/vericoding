// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<(i8, i8)>) -> (sorted: Vec<(i8, i8)>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> less_eq((sorted[i].0 as int, sorted[i].1 as int), (sorted[j].0 as int, sorted[j].1 as int)),
        sorted@.len() == s@.len(),
        s@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == sorted@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation errors by correcting type inconsistencies in invariants and changing j to int to prevent underflow */
{
    let mut result: Vec<(i8, i8)> = s.clone();
    let mut i: usize = 1;
    while i < result.len()
        invariant
            forall |j: int, k: int| #![trigger less_eq((result@[j].0 as int, result@[j].1 as int), (result@[k].0 as int, result@[k].1 as int))]
                0 <= j && j < k && k < i as int ==> less_eq((result@[j].0 as int, result@[j].1 as int), (result@[k].0 as int, result@[k].1 as int)),
            result@.len() == s@.len(),
            s@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == result@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset(),
        decreases (s@.len() - i)
    {
        let key = result@[i];
        let key_int = (key.0 as int, key.1 as int);
        let mut j: int = (i - 1) as int;
        while j >= 0 && less((result@[j as usize].0 as int, result@[j as usize].1 as int), key_int)
            invariant
                0 <= j + 1 && j + 1 <= i as int,
                forall |p: int| 0 <= p && p <= j ==> less_eq((result@[p as usize].0 as int, result@[p as usize].1 as int), key_int),
                forall |p: int, q: int| 0 <= p && p < q && q <= i as int && p != j + 1 ==> less_eq((result@[p as usize].0 as int, result@[p as usize].1 as int), (result@[q as usize].0 as int, result@[q as usize].1 as int)),
                forall |p: int| (j < p && p <= i as int) ==> less_eq(key_int, (result@[p as usize].0 as int, result@[p as usize].1 as int)),
                result@.len() == s@.len(),
                s@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == result@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset(),
                key_int == (key.0 as int, key.1 as int)
            decreases (j as nat + 1)
        {
            result = result.set(j as usize + 1, result@[j as usize]);
            j = j - 1;
        }
        result = result.set(j as usize + 1, key);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}