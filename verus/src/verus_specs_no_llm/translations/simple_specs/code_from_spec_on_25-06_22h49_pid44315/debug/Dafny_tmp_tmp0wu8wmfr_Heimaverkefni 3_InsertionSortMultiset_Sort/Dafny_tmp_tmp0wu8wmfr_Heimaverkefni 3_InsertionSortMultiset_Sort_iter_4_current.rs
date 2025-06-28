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
    assert(forall|i: int| k_int <= i < s.len() ==> s[i] >= x) by {
        if k < s.len() {
            // We broke because s[k] >= x
            assert(s[k_int] >= x);
        }
        // Use the sorted property
        if exists|i: int| k_int <= i < s.len() && s[i] < x {
            let bad_i = choose|i: int| k_int <= i < s.len() && s[i] < x;
            if k < s.len() {
                assert(k_int <= bad_i < s.len());
                assert(s[k_int] >= x);
                assert(s[bad_i] < x);
                if k_int < bad_i {
                    assert(s[k_int] <= s[bad_i]); // from sorted property
                    assert(false); // contradiction
                }
            }
            if k == s.len() {
                // We went through entire array, so all elements < k are <= x
                assert(bad_i < k_int); // contradiction with bad_i >= k_int
                assert(false);
            }
        }
    };
    
    // Subrange properties follow from the above
    assert(s == s.subrange(0, k_int) + s.subrange(k_int, s.len() as int));
    
    k_int
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
        let old_len = result.len();
        
        // Insert value at position j
        result = result.subrange(0, ji) + seq![value] + result.subrange(ji, old_len as int);
        
        // Prove length preservation
        assert(result.len() == old_len + 1);
        assert(result.len() == i + 1);
        
        // Prove sorted property
        assert(forall|k: int| 0 <= k < ji ==> result[k] <= value);
        assert(forall|k: int| ji + 1 <= k < result.len() ==> value <= result[k]) by {
            // Elements after insertion position were >= value in old_result
            assert(forall|k: int| ji <= k < old_len ==> value <= old_result[k]);
        };
        
        assert(forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]) by {
            // Case analysis on where p and q fall relative to insertion point
            assert(forall|p: int, q: int| 0 <= p < q < old_len ==> old_result[p] <= old_result[q]);
        };
        
        // Prove multiset preservation
        assert(multiset![result] == multiset![old_result] + multiset![seq![value]]);
        assert(multiset![seq![value]] == multiset![m.subrange(ii, ii + 1)]);
        assert(multiset![old_result] == multiset![m.subrange(0, ii)]);
        assert(m.subrange(0, ii) + m.subrange(ii, ii + 1) == m.subrange(0, ii + 1));
        assert(multiset![m.subrange(0, ii)] + multiset![m.subrange(ii, ii + 1)] == multiset![m.subrange(0, ii + 1)]);
        assert(multiset![result] == multiset![m.subrange(0, ii + 1)]);
        
        i = i + 1;
    }
    
    assert(i == m.len());
    assert(m.subrange(0, m.len() as int) == m);
    assert(multiset![result] == multiset![m]);
    
    result
}

}