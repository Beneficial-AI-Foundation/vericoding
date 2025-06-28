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
    let mut k = 0;
    
    while k < s.len()
        invariant 0 <= k <= s.len()
        invariant forall|i: int| 0 <= i < k ==> s[i] <= x
    {
        if s[k] >= x {
            break;
        }
        k = k + 1;
    }
    
    // Proof assertions to help verify postconditions
    assert(forall|i: int| k <= i < s.len() ==> s[i] >= x) by {
        if k < s.len() {
            assert(s[k] >= x);
            // Use the sorted property to prove the rest
            assert(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]);
        }
    };
    
    assert(s == s.subrange(0, k) + s.subrange(k, s.len() as int)) by {
        assert(s.subrange(0, s.len() as int) == s);
    };
    
    k
}

fn Sort(m: Seq<int>) -> (r: Seq<int>)
    ensures r.len() == m.len()
    ensures forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q]
    ensures multiset![r] == multiset![m]
{
    if m.len() == 0 {
        return seq![];
    }
    
    // Simple insertion sort implementation
    let mut result = seq![m[0]];
    let mut i = 1;
    
    while i < m.len()
        invariant 1 <= i <= m.len()
        invariant result.len() == i
        invariant forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]
        invariant multiset![result] == multiset![m.subrange(0, i)]
    {
        let value = m[i];
        let mut j = 0;
        
        // Find insertion position
        while j < result.len() && result[j] <= value
            invariant 0 <= j <= result.len()
            invariant forall|k: int| 0 <= k < j ==> result[k] <= value
        {
            j = j + 1;
        }
        
        // Store old result for multiset reasoning
        let old_result = result;
        
        // Insert value at position j
        result = result.subrange(0, j) + seq![value] + result.subrange(j, result.len() as int);
        
        // Proof assertions for multiset preservation
        assert(old_result == result.subrange(0, j) + result.subrange(j, old_result.len() as int)) by {
            assert(result.subrange(j, old_result.len() as int) == old_result.subrange(j, old_result.len() as int));
        };
        
        assert(multiset![result] == multiset![old_result] + multiset![seq![value]]) by {
            assert(result == result.subrange(0, j) + seq![value] + result.subrange(j+1, result.len() as int));
        };
        
        assert(multiset![old_result] == multiset![m.subrange(0, i)]);
        assert(multiset![seq![value]] == multiset![m.subrange(i, i+1)]);
        assert(m.subrange(0, i) + m.subrange(i, i+1) == m.subrange(0, i+1));
        
        // Proof for sorted property
        assert(forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]) by {
            assert(forall|k: int| 0 <= k < j ==> result[k] <= value);
            assert(forall|k: int| j < k < result.len() ==> value <= result[k]);
            assert(forall|p: int, q: int| 0 <= p < q < old_result.len() ==> old_result[p] <= old_result[q]);
        };
        
        i = i + 1;
    }
    
    // Final proof that multiset is preserved
    assert(multiset![result] == multiset![m.subrange(0, m.len() as int)]);
    assert(m.subrange(0, m.len() as int) == m);
    
    result
}

}