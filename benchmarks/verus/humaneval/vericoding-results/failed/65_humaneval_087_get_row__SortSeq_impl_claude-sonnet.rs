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
spec fn is_sorted(s: Seq<(i8, i8)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> less_eq((s[i].0 as int, s[i].1 as int), (s[j].0 as int, s[j].1 as int))
}

spec fn multiset_equal(s1: Seq<(i8, i8)>, s2: Seq<(i8, i8)>) -> bool {
    s1.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset() == s2.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)).to_multiset()
}

/* helper modified by LLM (iteration 5): fixed bubble sort step to use ghost variables for int types */
fn bubble_sort_step(v: &mut Vec<(i8, i8)>, end: usize)
    requires
        old(v).len() > 0,
        end <= old(v).len()
    ensures
        v.len() == old(v).len(),
        multiset_equal(v@, old(v)@),
        end > 0 ==> forall|i: int| 0 <= i < end - 1 ==> less_eq((v[i].0 as int, v[i].1 as int), (v[i + 1].0 as int, v[i + 1].1 as int))
{
    if end <= 1 {
        return;
    }
    
    let mut i = 0;
    while i < end - 1
        invariant
            0 <= i <= end - 1,
            end <= v.len(),
            v.len() == old(v).len(),
            multiset_equal(v@, old(v)@),
            forall|k: int| 0 <= k < i ==> less_eq((v[k].0 as int, v[k].1 as int), (v[k + 1].0 as int, v[k + 1].1 as int))
    {
        proof {
            let curr = (v[i].0 as int, v[i].1 as int);
            let next = (v[i + 1].0 as int, v[i + 1].1 as int);
            
            if !less_eq(curr, next) {
                let temp = v[i];
                v.set(i, v[i + 1]);
                v.set(i + 1, temp);
            }
        }
        
        if v[i].0 > v[i + 1].0 || (v[i].0 == v[i + 1].0 && v[i].1 < v[i + 1].1) {
            let temp = v[i];
            v.set(i, v[i + 1]);
            v.set(i + 1, temp);
        }
        i = i + 1;
    }
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
    /* code modified by LLM (iteration 5): simplified to basic bubble sort without helper function */
    let mut result = s;
    let len = result.len();
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == s.len(),
            multiset_equal(result@, s@),
            forall|k: int, l: int| i <= k < l < result.len() ==> less_eq((result[k].0 as int, result[k].1 as int), (result[l].0 as int, result[l].1 as int))
        decreases len - i
    {
        let mut j = 0;
        while j < len - i - 1
            invariant
                0 <= j <= len - i - 1,
                result.len() == s.len(),
                multiset_equal(result@, s@),
                forall|k: int, l: int| i <= k < l < result.len() ==> less_eq((result[k].0 as int, result[k].1 as int), (result[l].0 as int, result[l].1 as int))
        {
            if result[j].0 > result[j + 1].0 || (result[j].0 == result[j + 1].0 && result[j].1 < result[j + 1].1) {
                let temp = result[j];
                result.set(j, result[j + 1]);
                result.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}