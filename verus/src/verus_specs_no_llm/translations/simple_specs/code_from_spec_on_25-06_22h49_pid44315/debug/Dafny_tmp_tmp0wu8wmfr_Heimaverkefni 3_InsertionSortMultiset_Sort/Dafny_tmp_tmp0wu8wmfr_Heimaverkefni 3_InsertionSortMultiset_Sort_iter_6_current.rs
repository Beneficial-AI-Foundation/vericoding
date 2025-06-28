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
            if k_int < s.len() {
                // We broke because s[k] >= x, and array is sorted
                assert(s[k_int] >= x);
                if k_int < i {
                    // Use sorted property
                    assert(s[k_int] <= s[i]); // from sorted property
                    assert(s[i] >= s[k_int]);
                    assert(s[i] >= x);
                }
            }
        };
        
        // Subrange properties follow from element-wise properties
        assert forall|z: int| z in s.subrange(0, k_int) implies z <= x by {
            // If z is in the subrange, there exists an index where s[idx] == z
            assert exists|idx: int| 0 <= idx < k_int && s[idx] == z;
            let idx = choose|idx: int| 0 <= idx < k_int && s[idx] == z;
            assert(s[idx] <= x);
        };
        
        assert forall|z: int| z in s.subrange(k_int, s.len() as int) implies z >= x by {
            assert exists|idx: int| k_int <= idx < s.len() && s[idx] == z;
            let idx = choose|idx: int| k_int <= idx < s.len() && s[idx] == z;
            assert(s[idx] >= x);
        };
        
        // Sequence concatenation property
        assert(s =~= s.subrange(0, k_int) + s.subrange(k_int, s.len() as int));
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
                    assert(value <= old_result[q - 1]);
                } else if p == ji && q > ji {
                    // p is inserted element, q in last part
                    assert(result[p] == value);
                    assert(result[q] == old_result[q - 1]);
                    if j < old_len {
                        assert(value <= old_result[j as int]);
                        if q - 1 >= j {
                            assert(old_result[j as int] <= old_result[q - 1]);
                        }
                    }
                } else {
                    // Both in last part (p > ji && q > ji)
                    assert(result[p] == old_result[p - 1]);
                    assert(result[q] == old_result[q - 1]);
                    assert(old_result[p - 1] <= old_result[q - 1]);
                }
            };
            
            // Prove multiset preservation
            assert(multiset![result] =~= multiset![old_result] + multiset![seq![value]]);
            assert(multiset![seq![value]] =~= multiset![m.subrange(ii, ii + 1)]);
            assert(multiset![old_result] =~= multiset![m.subrange(0, ii)]);
            
            // Prove that combining subranges gives us the right result
            assert(m.subrange(0, ii) + m.subrange(ii, ii + 1) =~= m.subrange(0, ii + 1));
            assert(multiset![m.subrange(0, ii)] + multiset![m.subrange(ii, ii + 1)] =~= multiset![m.subrange(0, ii + 1)]);
            assert(multiset![result] =~= multiset![m.subrange(0, ii + 1)]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == m.len());
        assert(m.subrange(0, m.len() as int) =~= m);
        assert(multiset![result] =~= multiset![m]);
    }
    
    result
}

}