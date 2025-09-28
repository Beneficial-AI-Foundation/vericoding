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


proof fn lemma_less_transitive(a: (int, int), b: (int, int), c: (int, int))
    requires
        less(a, b),
        less(b, c),
    ensures
        less(a, c),
{
    let (x1, y1) = a;
    let (x2, y2) = b;
    let (x3, y3) = c;
    
    if x1 < x2 {
        if x2 < x3 {
            // x1 < x2 < x3
        } else if x2 == x3 {
            // x1 < x2 == x3
        }
    } else if x1 == x2 {
        if y1 > y2 {
            if x2 < x3 {
                // x1 == x2 < x3
            } else if x2 == x3 {
                // x1 == x2 == x3, y1 > y2 and y2 > y3
                assert(y1 > y3);
            }
        }
    }
}

proof fn lemma_less_eq_transitive(a: (int, int), b: (int, int), c: (int, int))
    requires
        less_eq(a, b),
        less_eq(b, c),
    ensures
        less_eq(a, c),
{
    if a == b {
    } else if b == c {
    } else {
        lemma_less_transitive(a, b, c);
    }
}

proof fn lemma_less_eq_reflexive(a: (int, int))
    ensures
        less_eq(a, a),
{
}

fn insert_sorted(mut v: Vec<(i8, i8)>, idx: usize, elem: (i8, i8)) -> (result: Vec<(i8, i8)>)
    requires
        idx <= v@.len(),
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> less_eq((v[i].0 as int, v[i].1 as int), (v[j].0 as int, v[j].1 as int)),
    ensures
        result@.len() == v@.len() + 1,
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> less_eq((result[i].0 as int, result[i].1 as int), (result[j].0 as int, result[j].1 as int)),
        result@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == v@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset().insert((elem.0 as int, elem.1 as int)),
{
    /* helper modified by LLM (iteration 5): Fixed decreases clause in insert_sorted */
    let mut i = v.len();
    v.push(elem);
    
    let ghost old_v = v@;
    
    while i > idx
        invariant
            0 <= i <= v@.len() - 1,
            forall|k: int, l: int| 0 <= k < l < v@.len() && (l != i || k != i - 1) ==> less_eq((v[k].0 as int, v[k].1 as int), (v[l].0 as int, v[l].1 as int)),
            v@.map(|k: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == old_v.map(|k: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset().insert((elem.0 as int, elem.1 as int)),
        decreases i,
    {
        let temp = v[i];
        v.set(i, v[i - 1]);
        v.set(i - 1, temp);
        i = i - 1;
    }
    
    v
}



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
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut sorted = Vec::new();
    
    for i in 0..s.len() {
        let elem = s[i];
        let mut insert_idx = 0;
        
        while insert_idx < sorted.len()
            decreases sorted.len() - insert_idx,
        {
            let current_elem: (i8, i8) = sorted[insert_idx];
            proof {
                let a = (current_elem.0 as int, current_elem.1 as int);
                let b = (elem.0 as int, elem.1 as int);
            }
            if current_elem.0 < elem.0 || (current_elem.0 == elem.0 && current_elem.1 > elem.1) {
                insert_idx += 1;
            } else {
                break;
            }
        }
        
        sorted = insert_sorted(sorted, insert_idx, elem);
    }
    
    sorted
}
// </vc-code>


}

fn main() {}