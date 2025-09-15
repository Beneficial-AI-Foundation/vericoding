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
/* helper modified by LLM (iteration 4): Fixing Multiset type errors and method calls */
proof fn lemma_smaller_head_preserves_sorted(a: Seq<i32>, b: Seq<i32>, x: i32, y: i32)
    requires
        is_sorted(a),
        is_sorted(b),
        0 < a.len(),
        0 < b.len(),
        x == a[0],
        y == b[0],
    ensures
        x <= y ==> (forall|i: int| 1 <= i < a.len() as int ==> x <= a[i]) && is_sorted(a.subrange(1, a.len() as int))
{
}

proof fn lemma_merge_step_preserves_sorted(prefix: Seq<i32>, a: Seq<i32>, b: Seq<i32>, elem: i32)
    requires
        is_sorted(prefix),
        is_sorted(a),
        is_sorted(b),
        (prefix.len() == 0 ==> true) && (prefix.len() > 0 ==> elem >= prefix[prefix.len() - 1]),
        (a.len() > 0 && b.len() > 0) ==> (a[0] <= b[0] ==> elem <= a[0]) && (b[0] <= a[0] ==> elem <= b[0]),
        (a.len() > 0 && b.len() == 0) ==> elem <= a[0],
        (a.len() == 0 && b.len() > 0) ==> elem <= b[0],
    ensures
        is_sorted(prefix.push(elem))
{
}

proof fn lemma_merge_step_preserves_multiset(prefix: Seq<i32>, a: Seq<i32>, b: Seq<i32>, elem: i32, new_prefix: Seq<i32>, new_a: Seq<i32>, new_b: Seq<i32>)
    requires
        new_prefix == prefix.push(elem),
        (a.len() > 0 && elem == a[0]) ==> (new_a == a.subrange(1, a.len() as int) && new_b == b),
        (b.len() > 0 && elem == b[0]) ==> (new_b == b.subrange(1, b.len() as int) && new_a == a),
        (a.len() == 0 && elem == b[0]) ==> (new_b == b.subrange(1, b.len() as int) && new_a == a),
        (b.len() == 0 && elem == a[0]) ==> (new_a == a.subrange(1, a.len() as int) && new_b == b),
    ensures
        new_prefix.to_multiset() == prefix.to_multiset().insert(elem),
        new_a.to_multiset() + new_b.to_multiset() == a.to_multiset() + b.to_multiset().remove(elem).remove(elem)
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
/* code modified by LLM (iteration 4): Fixing multiset method calls and proof operations */
{
    let mut result = Vec::new();
    let mut a_ptr = 0;
    let mut b_ptr = 0;
    
    while a_ptr < a.len() || b_ptr < b.len()
        invariant
            a_ptr <= a.len(),
            b_ptr <= b.len(),
            is_sorted(result@),
            result@.to_multiset() + a@.subrange(a_ptr as int, a.len() as int).to_multiset() + b@.subrange(b_ptr as int, b.len() as int).to_multiset() 
                == a@.to_multiset() + b@.to_multiset(),
            (result.len() == 0 ==> true) && (result.len() > 0 ==> 
                (a_ptr < a.len() ==> result[result.len() - 1] <= a@[a_ptr as int]) && 
                (b_ptr < b.len() ==> result[result.len() - 1] <= b@[b_ptr as int]))
    {
        if a_ptr < a.len() && (b_ptr >= b.len() || a[a_ptr] <= b[b_ptr]) {
            let elem = a[a_ptr];
            result.push(elem);
            a_ptr += 1;
        } else {
            let elem = b[b_ptr];
            result.push(elem);
            b_ptr += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}