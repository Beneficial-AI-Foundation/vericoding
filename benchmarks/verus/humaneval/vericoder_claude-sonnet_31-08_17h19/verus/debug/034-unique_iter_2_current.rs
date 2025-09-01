use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
proof fn lemma_insert_maintains_sorted(v: Vec<i32>, x: i32, pos: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j],
        0 <= pos <= v.len(),
        forall|i: int| 0 <= i < pos ==> v[i] < x,
        forall|i: int| pos <= i < v.len() ==> x < v[i],
    ensures
        ({
            let mut result = v;
            result.insert(pos, x);
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j]
        })
{
    let mut result = v;
    result.insert(pos, x);
    
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] < result[j] by {
        if i < pos && j == pos {
            assert(result[i] == v[i]);
            assert(result[j] == x);
            assert(v[i] < x);
        } else if i == pos && j > pos {
            assert(result[i] == x);
            assert(result[j] == v[j - 1]);
            assert(x < v[j - 1]);
        } else if i < pos && j > pos {
            assert(result[i] == v[i]);
            assert(result[j] == v[j - 1]);
            assert(v[i] < x);
            assert(x < v[j - 1]);
            assert(v[i] < v[j - 1]);
        } else if i < pos && j < pos {
            assert(result[i] == v[i]);
            assert(result[j] == v[j]);
            assert(v[i] < v[j]);
        } else if i >= pos && j > pos {
            assert(result[i] == v[i - 1]);
            assert(result[j] == v[j - 1]);
            assert(v[i - 1] < v[j - 1]);
        }
    }
}

proof fn lemma_binary_search_bounds(v: Vec<i32>, x: i32, pos: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j],
        pos <= v.len(),
        (pos == 0 || v[pos as int - 1] < x),
        (pos == v.len() || x <= v[pos as int]),
    ensures
        forall|i: int| 0 <= i < pos ==> v[i] < x,
        forall|i: int| pos <= i < v.len() ==> x <= v[i],
{
    assert forall|i: int| 0 <= i < pos implies v[i] < x by {
        if pos > 0 && i < pos {
            if i == pos - 1 {
                assert(v[i] < x);
            } else {
                assert(v[i] < v[pos as int - 1]);
                assert(v[pos as int - 1] < x);
                assert(v[i] < x);
            }
        }
    }
    
    assert forall|i: int| pos <= i < v.len() implies x <= v[i] by {
        if pos < v.len() && i >= pos {
            if i == pos {
                assert(x <= v[i]);
            } else {
                assert(v[pos as int] <= v[i]);
                assert(x <= v[pos as int]);
                assert(x <= v[i]);
            }
        }
    }
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
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..s.len()
        invariant
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] < result[k],
            forall|j: int| #![auto] 0 <= j < result.len() ==> s@.contains(result[j]),
            forall|j: int| #![trigger s[j]] 0 <= j < i ==> result@.contains(s[j]),
    {
        let x = s[i];
        
        if !result@.contains(x) {
            let mut pos = 0;
            
            while pos < result.len() && result[pos as int] < x
                invariant
                    0 <= pos <= result.len(),
                    forall|j: int| 0 <= j < pos ==> result[j] < x,
                    forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] < result[k],
            {
                pos += 1;
            }
            
            proof {
                lemma_binary_search_bounds(result, x, pos);
            }
            
            result.insert(pos, x);
            
            proof {
                lemma_insert_maintains_sorted(result, x, pos);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}