use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
use vstd::relations::total_ordering;
use vstd::prelude::*;

proof fn lemma_sorted_unique<T: SpecOrd>(s: Seq<T>) 
    requires
        total_ordering::<T>(|a: T, b: T| a.spec_lt(b)),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].spec_lt(s[j]),
    ensures
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j],
{
}

proof fn lemma_seq_sorted_contains<T: SpecOrd>(s: Seq<T>, x: T, start: int, end: int)
    requires
        total_ordering::<T>(|a: T, b: T| a.spec_lt(b)),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].spec_lt(s[j]),
        0 <= start <= end <= s.len(),
    ensures
        s.contains(x) == (exists|i: int| start <= i < end && s[i] == x),
    decreases end - start,
{
    if start >= end {
    } else {
        let mid = start + (end - start) / 2;
        if s[mid] == x {
        } else if s[mid].spec_lt(x) {
            lemma_seq_sorted_contains(s, x, mid + 1, end);
        } else {
            lemma_seq_sorted_contains(s, x, start, mid);
        }
    }
}

proof fn lemma_vec_to_seq_sorted<T: SpecOrd>(v: Vec<T>, s: Seq<T>)
    requires
        total_ordering::<T>(|a: T, b: T| a.spec_lt(b)),
        v@ == s,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i].spec_lt(v[j]),
    ensures
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].spec_lt(s[j]),
{
}

proof fn lemma_vec_contains_seq_contains<T: PartialEq + Eq>(v: Vec<T>, s: Seq<T>, x: T)
    requires
        v@ == s,
    ensures
        v.contains(&x) == s.contains(x),
{
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sorted = s.clone();
    sorted.sort();
    proof {
        lemma_multiset_commutative(s@, sorted@);
    }
    
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] < result[l],
            forall|k: int| 0 <= k < result.len() ==> sorted@.contains(result[k]),
            forall|k: int| 0 <= k < i ==> (k == 0 || sorted[k-1] < sorted[k]) ==> result@.contains(sorted[k]),
        decreases sorted.len() - i,
    {
        if i == 0 || sorted[i-1] < sorted[i] {
            result.push(sorted[i]);
        }
        i = i + 1;
    }
    
    proof {
        total_ordering::<i32>(|a: i32, b: i32| a < b);
        lemma_vec_to_seq_sorted(sorted, sorted@);
        lemma_sorted_unique(sorted@);
        
        assert forall|k: int| 0 <= k < result.len() implies s@.contains(result[k]) by {
            assert(sorted@.contains(result[k]));
        }
        
        assert forall|k: int| 0 <= k < s.len() implies result@.contains(s[k]) by {
            assert(sorted@.contains(s[k]));
            lemma_seq_sorted_contains(sorted@, s[k], 0, sorted.len() as int);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}