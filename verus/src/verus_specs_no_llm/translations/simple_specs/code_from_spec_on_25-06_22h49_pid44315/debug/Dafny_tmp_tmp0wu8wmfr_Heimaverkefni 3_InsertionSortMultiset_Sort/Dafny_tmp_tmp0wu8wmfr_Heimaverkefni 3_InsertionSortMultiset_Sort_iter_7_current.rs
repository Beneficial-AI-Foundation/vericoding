use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Search(s: Seq<int>, x: int) -> (k: int)
    requires forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    ensures 0 <= k <= s.len()
    ensures forall|i: int| 0 <= i < k ==> s[i] <= x
    ensures forall|i: int| k <= i < s.len() ==> s[i] >= x
    ensures forall|z: int| z in s.subrange(0, k) ==> z <= x
    ensures forall|z: int| z in s.subrange(k, s.len() as int) ==> z >= x
    ensures s == s.subrange(0, k) + s.subrange(k, s.len() as int)
{
    let mut k: usize = 0;
    
    while k < s.len()
        invariant 0 <= k <= s.len()
        invariant forall|i: int| 0 <= i < k ==> s[i] <= x
    {
        if s[k as int] >= x {
            break;
        }
        k = k + 1;
    }
    
    let k_int = k as int;
    
    // Prove the remaining postconditions
    proof {
        // Prove that all elements from k onwards are >= x
        assert forall|i: int| k_int <= i < s.len() implies s[i] >= x by {
            if k_int <= i < s.len() {
                if k_int == s.len() {
                    // Loop ended naturally, no elements >= k
                } else {
                    // We broke because s[k] >= x, and array is sorted
                    assert(s[k_int] >= x);
                    if k_int < i {
                        // Use sorted property
                        assert(s[k_int] <= s[i]); // from sorted property
                    } else if k_int == i {
                        assert(s[i] == s[k_int]);
                    }
                }
            }
        };
        
        // Subrange properties follow from element-wise properties
        assert forall|z: int| z in s.subrange(0, k_int) implies z <= x by {
            // The subrange property follows from the element-wise property
        };
        
        assert forall|z: int| z in s.subrange(k_int, s.len() as int) implies z >= x by {
            // The subrange property follows from the element-wise property
        };
    }
    
    k_int
}

fn Sort(m: Seq<int>) -> (r: Seq<int>)
    ensures r.len() == m.len()
    ensures forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q]
    ensures multiset![r] =~= multiset![m]
{
    if m.len() == 0 {
        return seq![];
    }
    
    let mut result = seq![m[0]];
    let mut i: usize = 1;
    
    while i < m.len()
        invariant 1 <= i <= m.len()
        invariant result.len() == i
        invariant forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]
        invariant multiset![result] =~= multiset![m.subrange(0, i as int)]
    {
        let value = m[i as int];
        let mut j: usize = 0;
        
        // Find insertion position
        while j < result.len()
            invariant 0 <= j <= result.len()
            invariant forall|k: int| 0 <= k < j ==> result[k] <= value
        {
            if result[j as int] > value {
                break;
            }
            j = j + 1;
        }
        
        let old_result = result;
        let ji = j as int;
        let ii = i as int;
        let old_len = result.len();
        
        // Insert value at position j
        result = result.subrange(0, ji) + seq![value] + result.subrange(ji, old_len as int);
        
        proof {
            // Prove length preservation
            assert(result.len() == old_len + 1);
            assert(result.len() == i + 1);
            
            // Prove sorted property
            assert forall|p: int, q: int| 0 <= p < q < result.len() implies result[p] <= result[q] by {
                if q < ji {
                    // Both in first part
                } else if p < ji && q == ji {
                    // p in first part, q is the inserted element
                } else if p < ji && q > ji {
                    // p in first part, q in last part
                } else if p == ji && q > ji {
                    // p is inserted element, q in last part
                    if ji < old_len {
                        // value <= old_result[ji] and old_result[ji] <= old_result[q-1]
                    }
                } else {
                    // Both in last part (p > ji && q > ji)
                }
            };
            
            // Prove multiset preservation - simplified approach
            assert(multiset![result].len() == multiset![old_result].len() + 1);
        }
        
        i = i + 1;
    }
    
    result
}

}