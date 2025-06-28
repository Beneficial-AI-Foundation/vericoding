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
        invariant s == s.subrange(0, k as int) + s.subrange(k as int, s.len() as int)
    {
        if s[k as int] >= x {
            break;
        }
        k = k + 1;
    }
    
    let k_int = k as int;
    
    proof {
        // Prove that all elements from k onwards are >= x
        assert forall|i: int| k_int <= i < s.len() implies s[i] >= x by {
            if k_int <= i < s.len() {
                if k_int == s.len() {
                    // Empty range, vacuously true
                    assert(false);
                } else {
                    // We broke because s[k] >= x, and array is sorted
                    assert(s[k_int] >= x);
                    if k_int < i {
                        // Use sorted property: since k <= i and array is sorted
                        assert(s[k_int] <= s[i]);
                        assert(s[i] >= s[k_int] >= x);
                    } else if k_int == i {
                        assert(s[i] == s[k_int] >= x);
                    }
                }
            }
        };
        
        // Subrange properties follow from element-wise properties
        assert forall|z: int| z in s.subrange(0, k_int) implies z <= x by {
            if z in s.subrange(0, k_int) {
                let idx = choose|j: int| 0 <= j < k_int && s[j] == z;
                assert(s[idx] <= x);
            }
        };
        
        assert forall|z: int| z in s.subrange(k_int, s.len() as int) implies z >= x by {
            if z in s.subrange(k_int, s.len() as int) {
                let idx = choose|j: int| k_int <= j < s.len() && s[j] == z;
                assert(s[idx] >= x);
            }
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
                if 0 <= p < q < result.len() {
                    if q < ji {
                        // Both in first part - maintains old ordering
                        assert(result[p] == old_result[p]);
                        assert(result[q] == old_result[q]);
                        assert(old_result[p] <= old_result[q]);
                    } else if p < ji && q == ji {
                        // p in first part, q is the inserted element
                        assert(result[p] == old_result[p]);
                        assert(result[q] == value);
                        assert(old_result[p] <= value);
                    } else if p < ji && q > ji {
                        // p in first part, q in last part
                        assert(result[p] == old_result[p]);
                        assert(result[q] == old_result[q - 1]);
                        assert(old_result[p] <= value);
                        if ji < old_len {
                            assert(value <= old_result[ji]);
                            assert(old_result[ji] == old_result[q - 1]);
                        }
                        assert(result[p] <= result[q]);
                    } else if p == ji && q > ji {
                        // p is inserted element, q in last part  
                        assert(result[p] == value);
                        assert(result[q] == old_result[q - 1]);
                        if ji < old_len {
                            assert(value <= old_result[ji]);
                            assert(old_result[ji] <= old_result[q - 1]);
                        }
                    } else {
                        // Both in last part (p > ji && q > ji)
                        assert(result[p] == old_result[p - 1]);
                        assert(result[q] == old_result[q - 1]);
                        assert(old_result[p - 1] <= old_result[q - 1]);
                    }
                }
            };
            
            // Prove multiset preservation
            assert(multiset![old_result].insert(value) =~= multiset![result]);
            assert(multiset![m.subrange(0, ii)] =~= multiset![old_result]);
            assert(m[ii] == value);
            assert(multiset![m.subrange(0, ii + 1)] =~= multiset![m.subrange(0, ii)].insert(m[ii]));
            assert(multiset![result] =~= multiset![m.subrange(0, ii + 1)]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == m.len());
        assert(multiset![result] =~= multiset![m.subrange(0, m.len() as int)]);
        assert(m.subrange(0, m.len() as int) == m);
    }
    
    result
}

}