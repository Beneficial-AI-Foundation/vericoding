// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j]
}

/* helper modified by LLM (iteration 3): added decreases clause to loop */
fn insert_sorted(mut v: Vec<i32>, x: i32) -> (result: Vec<i32>)
    requires
        is_sorted(v),
        !v@.contains(x),
    ensures
        is_sorted(result),
        result.len() == v.len() + 1,
        result@.contains(x),
        forall|i: int| 0 <= i < v.len() ==> result@.contains(v[i]),
{
    let mut i = 0;
    while i < v.len() && v[i] < x
        invariant
            0 <= i <= v.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> v[j] < v[k],
            forall|j: int| i <= j < v.len() ==> x < v[j],
        decreases v.len() - i,
    {
        i += 1;
    }
    
    v.insert(i, x);
    v
}

/* helper modified by LLM (iteration 4): added decreases clause to loop in exec_contains */
fn exec_contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures result <==> v@.contains(x)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j] != x,
            v@.contains(x) <==> (exists|j: int| i <= j < v.len() && v[j] == x),
        decreases v.len() - i,
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotation in invariant */
    let mut result = Vec::new();
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            is_sorted(result),
            forall|j: int| 0 <= j < i ==> result@.contains(s[j]),
            forall|j: int| 0 <= j < result.len() ==> exists|k: int| 0 <= k < i && s[k] == #[trigger] result[j],
    {
        if !exec_contains(&result, s[i]) {
            result = insert_sorted(result, s[i]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}