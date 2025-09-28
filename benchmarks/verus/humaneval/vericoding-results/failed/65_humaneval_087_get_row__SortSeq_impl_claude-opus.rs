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

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<(i8, i8)>) -> (sorted: Vec<(i8, i8)>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> less_eq((sorted[i].0 as int, sorted[i].1 as int), (sorted[j].0 as int, sorted[j].1 as int)),
        sorted@.len() == s@.len(),
        s@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == sorted@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut sorted = s.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n - 1
        invariant
            sorted@.len() == s@.len(),
            sorted@.len() == n,
            s@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == sorted@.map(|idx: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset(),
            forall|k: int, l: int| 0 <= k < l <= i < sorted@.len() ==> less_eq((sorted[k].0 as int, sorted[k].1 as int), (sorted[l].0 as int, sorted[l].1 as int)),
            forall|k: int| 0 <= k <= i < sorted@.len() ==> forall|l: int| i < l < sorted@.len() ==> less_eq((sorted[k].0 as int, sorted[k].1 as int), (sorted[l].0 as int, sorted[l].1 as int)),
        decreases n - 1 - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                sorted@.len() == n,
                i < n,
                i < j <= n,
                i <= min_idx < j,
                min_idx < n,
                forall|k: int| i <= k < j ==> less_eq((sorted[min_idx].0 as int, sorted[min_idx].1 as int), (sorted[k].0 as int, sorted[k].1 as int)),
            decreases n - j
        {
            if sorted[j].0 < sorted[min_idx].0 || (sorted[j].0 == sorted[min_idx].0 && sorted[j].1 > sorted[min_idx].1) {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}