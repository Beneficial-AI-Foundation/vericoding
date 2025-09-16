// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

spec fn contains_all(result: Seq<i32>, s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> result.contains(s[i])
}

/* helper modified by LLM (iteration 4): Added spec function to check containment */
spec fn seq_contains(s: Seq<i32>, elem: i32) -> bool {
    s.contains(elem)
}

/* helper modified by LLM (iteration 4): Fixed parameter type from Vec<i32> to &Vec<i32> */
proof fn lemma_insert_maintains_sorted(v: &Vec<i32>, elem: i32, pos: usize)
    requires
        pos <= v.len(),
        sorted(v@),
        forall|i: int| 0 <= i < pos ==> v[i] < elem,
        forall|i: int| pos <= i < v.len() ==> elem < v[i],
    ensures
        sorted(v@.insert(pos as int, elem)),
{
    let s = v@;
    let new_s = s.insert(pos as int, elem);
    assert forall|i: int, j: int| 0 <= i < j < new_s.len() implies new_s[i] < new_s[j] by {
        if i < pos {
            if j == pos {
                assert(new_s[i] == s[i]);
                assert(new_s[j] == elem);
            } else if j < pos {
                assert(new_s[i] == s[i]);
                assert(new_s[j] == s[j]);
            } else {
                assert(new_s[i] == s[i]);
                assert(new_s[j] == s[j - 1]);
            }
        } else if i == pos {
            assert(new_s[i] == elem);
            assert(new_s[j] == s[j - 1]);
        } else {
            assert(new_s[i] == s[i - 1]);
            assert(new_s[j] == s[j - 1]);
        }
    }
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
    /* code modified by LLM (iteration 4): Added decreases clause to main loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            sorted(result@),
            forall|k: int| 0 <= k < result.len() ==> s@.contains(result[k]),
            forall|k: int| 0 <= k < i ==> result@.contains(s[k]),
            i <= s.len(),
        decreases s.len() - i
    {
        let elem = s[i];
        
        let ghost has_elem = result@.contains(elem);
        let mut found = false;
        let mut k: usize = 0;
        
        while k < result.len()
            invariant
                k <= result.len(),
                found <==> exists|m: int| 0 <= m < k && result[m] == elem,
            decreases result.len() - k
        {
            if result[k] == elem {
                found = true;
                break;
            }
            k = k + 1;
        }
        
        assert(found <==> has_elem);
        
        if !found {
            let mut j: usize = 0;
            
            while j < result.len()
                invariant
                    j <= result.len(),
                    sorted(result@),
                    forall|k: int| 0 <= k < j ==> result[k] < elem,
                decreases result.len() - j
            {
                if result[j] >= elem {
                    break;
                }
                j = j + 1;
            }
            
            assert(forall|k: int| j <= k < result.len() ==> elem < result[k]);
            
            proof {
                lemma_insert_maintains_sorted(&result, elem, j);
            }
            
            result.insert(j, elem);
            
            assert(result@.contains(elem));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}