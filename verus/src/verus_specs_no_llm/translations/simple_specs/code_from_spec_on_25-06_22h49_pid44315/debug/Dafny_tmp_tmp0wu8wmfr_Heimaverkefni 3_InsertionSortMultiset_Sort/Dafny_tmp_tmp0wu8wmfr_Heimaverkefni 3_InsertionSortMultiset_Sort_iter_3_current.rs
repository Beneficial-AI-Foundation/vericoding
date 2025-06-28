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
    
    // Proof for the remaining postconditions
    proof {
        // Show that all elements from k onwards are >= x
        if k < s.len() {
            // We broke because s[k] >= x
            assert(s[k as int] >= x);
            // Use sorted property to show rest
            let ki = k as int;
            assert(forall|i: int| ki <= i < s.len() ==> s[i] >= x) by {
                if exists|i: int| ki <= i < s.len() && s[i] < x {
                    let bad_i = choose|i: int| ki <= i < s.len() && s[i] < x;
                    assert(s[ki] >= x);
                    assert(s[bad_i] < x);
                    assert(ki <= bad_i);
                    if ki < bad_i {
                        assert(s[ki] <= s[bad_i]); // from sorted property
                        assert(false); // contradiction
                    } else {
                        assert(ki == bad_i);
                        assert(false); // contradiction
                    }
                }
            }
        } else {
            // k == s.len(), so the range [k, s.len()) is empty
            assert(forall|i: int| k <= i < s.len() ==> s[i] >= x);
        }
        
        // Subrange properties
        assert(forall|z: int| z in s.subrange(0, k as int) ==> z <= x) by {
            assert(forall|i: int| 0 <= i < k ==> s[i] <= x);
        }
        
        assert(forall|z: int| z in s.subrange(k as int, s.len() as int) ==> z >= x) by {
            assert(forall|i: int| k <= i < s.len() ==> s[i] >= x);
        }
        
        // Sequence equality
        assert(s == s.subrange(0, k as int) + s.subrange(k as int, s.len() as int));
    }
    
    k as int
}

fn Sort(m: Seq<int>) -> (r: Seq<int>)
    ensures r.len() == m.len()
    ensures forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q]
    ensures multiset![r] == multiset![m]
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
        invariant multiset![result] == multiset![m.subrange(0, i as int)]
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
        
        // Insert value at position j
        result = result.subrange(0, ji) + seq![value] + result.subrange(ji, result.len() as int);
        
        proof {
            // Prove multiset preservation
            assert(old_result == old_result.subrange(0, ji) + old_result.subrange(ji, old_result.len() as int));
            assert(result == old_result.subrange(0, ji) + seq![value] + old_result.subrange(ji, old_result.len() as int));
            
            // Multiset reasoning
            assert(multiset![result] == multiset![old_result.subrange(0, ji)] + multiset![seq![value]] + multiset![old_result.subrange(ji, old_result.len() as int)]);
            assert(multiset![old_result] == multiset![old_result.subrange(0, ji)] + multiset![old_result.subrange(ji, old_result.len() as int)]);
            assert(multiset![result] == multiset![old_result] + multiset![seq![value]]);
            
            assert(multiset![seq![value]] == multiset![m.subrange(ii, ii + 1)]);
            assert(multiset![old_result] == multiset![m.subrange(0, ii)]);
            assert(m.subrange(0, ii) + m.subrange(ii, ii + 1) == m.subrange(0, ii + 1));
            assert(multiset![result] == multiset![m.subrange(0, ii + 1)]);
            
            // Prove sorted property is maintained
            assert(forall|k: int| 0 <= k < ji ==> result[k] <= value);
            assert(forall|k: int| ji + 1 <= k < result.len() ==> value <= result[k]) by {
                assert(forall|k: int| ji <= k < old_result.len() ==> value <= old_result[k]);
            }
            
            assert(forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]) by {
                // The sorted property is preserved through the insertion
                assert(forall|p: int, q: int| 0 <= p < q < old_result.len() ==> old_result[p] <= old_result[q]);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(multiset![result] == multiset![m.subrange(0, m.len() as int)]);
        assert(m.subrange(0, m.len() as int) == m);
    }
    
    result
}

}