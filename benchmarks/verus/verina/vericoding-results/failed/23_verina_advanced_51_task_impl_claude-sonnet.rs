// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Multiset import error and updated helper functions */
use vstd::multiset::Multiset;

proof fn push_preserves_multiset<T>(v: Seq<T>, elem: T)
    ensures v.push(elem).to_multiset() == v.to_multiset().insert(elem)
{
}

proof fn subrange_extend_multiset<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i <= j < s.len()
    ensures s.subrange(0, j + 1).to_multiset() == s.subrange(0, j).to_multiset().insert(s[j])
{
}

proof fn push_preserves_sorted(v: Seq<i32>, elem: i32)
    requires is_sorted(v), v.len() > 0 ==> v[v.len() - 1] <= elem
    ensures is_sorted(v.push(elem))
{
}

proof fn multiset_add_commutative<T>(m1: vstd::multiset::Multiset<T>, m2: vstd::multiset::Multiset<T>)
    ensures m1.add(m2) == m2.add(m1)
{
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation without complex proof blocks */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a.len() && j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(b@.subrange(0, j as int).to_multiset())
        decreases a.len() + b.len() - i - j
    {
        if a[i] <= b[j] {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    
    while i < a.len()
        invariant
            i <= a.len(),
            j == b.len(),
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(b@.to_multiset())
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    while j < b.len()
        invariant
            i == a.len(),
            j <= b.len(),
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() == a@.to_multiset().add(b@.subrange(0, j as int).to_multiset())
        decreases b.len() - j
    {
        result.push(b[j]);
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}