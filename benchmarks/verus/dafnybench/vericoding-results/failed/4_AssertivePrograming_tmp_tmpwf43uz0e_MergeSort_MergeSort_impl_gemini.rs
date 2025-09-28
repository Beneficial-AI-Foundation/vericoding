// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) =~= a.subrange(0, i as int)) && 
    (a2.subrange(0, i as int) =~= a.subrange(mid as int, (i + mid) as int))
}

fn merge(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
{
  assume(false);
}

spec fn inv_sorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[(j + i - 1) as int] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[(j + i - 1) as int] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
    }

spec fn inv_sub_set(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by using correct Verus std library lemmas */
proof fn lemma_multiset_split_total(s: Seq<int>, m: int)
    requires 0 <= m <= s.len()
    ensures s.to_multiset() == s.subrange(0, m).to_multiset().add(s.subrange(m, s.len()).to_multiset())
{
    let s1 = s.subrange(0, m);
    let s2 = s.subrange(m, s.len());
    vstd::seq_lib::lemma_split_at_is_subrange(s, m);
    vstd::seq::lemma_add_commutes_with_to_multiset(s1, s2);
}
// </vc-helpers>

// <vc-spec>
fn merge_sort(a: Vec<int>) -> (b: Vec<int>)
    ensures
        b.len() == a.len(),
        sorted(b@),
        a@.to_multiset() == b@.to_multiset(),
    decreases a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used idiomatic vec! macro for vector creation */
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mid = n / 2;

    let mut a1 = Vec::with_capacity(mid);
    let mut i: usize = 0;
    while i < mid
        invariant
            i <= mid,
            a1@ == a@.subrange(0, i as int),
        decreases mid - i
    {
        a1.push(a[i]);
        i = i + 1;
    }

    let mut a2 = Vec::with_capacity(n - mid);
    i = mid;
    while i < n
        invariant
            mid <= i <= n,
            a1@ == a@.subrange(0, mid as int),
            a2@ == a@.subrange(mid as int, i as int),
        decreases n - i
    {
        a2.push(a[i]);
        i = i + 1;
    }

    proof {
        lemma_multiset_split_total(a@, mid as int);
    }

    let c = merge_sort(a1);
    let d = merge_sort(a2);

    let mut b = vec![0; n];
    
    merge(&mut b, &c, &d);

    b
}
// </vc-code>

}
fn main() {}