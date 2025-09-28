// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn inv(a: Seq<i32>, a1: Seq<i32>, a2: Seq<i32>, i: usize, mid: usize) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) == a.subrange(0, i as int)) && 
    (a2.subrange(0, i as int) == a.subrange(mid as int, (i + mid) as int))
}

fn merge_loop(b: &mut Vec<i32>, c: &Vec<i32>, d: &Vec<i32>, i0: usize, j0: usize) -> (usize, usize)
        requires
            old(b).len() == c.len() + d.len(),
            sorted(c@),
            sorted(d@),
            i0 <= c.len(),
            j0 <= d.len(),
            i0 + j0 <= old(b).len(),
            inv_sub_set(old(b)@, c@, d@, i0, j0),
            inv_sorted(old(b)@, c@, d@, i0, j0),
            i0 + j0 < old(b).len(),
{
    let mut i = i0;
    let mut j = j0;

    if i == c.len() || (j < d.len() && d[j] < c[i]) {

        b.set(i + j, d[j]);
        j = j + 1;
    } else {

        b.set(i + j, c[i]);
        i = i + 1;
    }

    (i, j)
}

spec fn inv_sorted(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[j + i - 1] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[j + i - 1] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
}

spec fn inv_sub_set(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in forall-by block */
proof fn lemma_sorted_extend(s: Seq<i32>, x: i32)
    requires
        sorted(s),
        s.len() > 0 ==> s.last() <= x,
    ensures
        sorted(s.push(x)),
{
    let s_new = s.push(x);
    assert forall|i: int, j: int| 0 <= i <= j < s_new.len() implies s_new[i] <= s_new[j] by {
        if j < s.len() {
        } else {
            if i < s.len() {
                if s.len() > 0 {
                }
            }
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn merge(b: &mut Vec<i32>, c: &Vec<i32>, d: &Vec<i32>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes, logic was not previously verified due to compilation error */
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i + j < b.len()
        invariant
            b.len() == c.len() + d.len(),
            sorted(c@),
            sorted(d@),
            i <= c.len(),
            j <= d.len(),
            inv_sorted(b@, c@, d@, i, j),
            inv_sub_set(b@, c@, d@, i, j),
        decreases b.len() - (i + j)
    {
        let old_b = b@;
        let k = i + j;

        if i < c.len() && (j >= d.len() || c[i] <= d[j]) {
            let item = c[i];
            b.set(k, item);

            proof {
                let prefix = old_b.subrange(0, k as int);
                lemma_sorted_extend(prefix, item);
            }
            
            i = i + 1;
        } else {
            assert(j < d.len()); 
            
            let item = d[j];
            b.set(k, item);

            proof {
                let prefix = old_b.subrange(0, k as int);
                lemma_sorted_extend(prefix, item);
            }
    
            j = j + 1;
        }
    }
}
// </vc-code>

}
fn main() {}