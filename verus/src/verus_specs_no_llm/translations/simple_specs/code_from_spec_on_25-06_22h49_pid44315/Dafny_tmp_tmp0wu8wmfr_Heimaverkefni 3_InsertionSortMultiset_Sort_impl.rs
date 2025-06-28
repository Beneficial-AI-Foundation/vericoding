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
        if k_int < s.len() {
            // If we exited the loop with k < s.len(), then s[k] >= x
            assert(s[k_int] >= x);
            // Use monotonicity of sorted sequence
            assert forall|i: int| k_int <= i < s.len() implies s[i] >= x by {
                if k_int <= i < s.len() {
                    assert(s[k_int] <= s[i]); // from sorted property
                }
            };
        }
        
        // Prove subrange properties
        assert forall|z: int| z in s.subrange(0, k_int) implies z <= x by {
            let sr = s.subrange(0, k_int);
            if z in sr {
                // Use the fact that subrange elements come from original indices
                assert exists|j: int| 0 <= j < k_int && s[j] == z;
            }
        };
        
        assert forall|z: int| z in s.subrange(k_int, s.len() as int) implies z >= x by {
            let sr = s.subrange(k_int, s.len() as int);
            if z in sr {
                // Use the fact that subrange elements come from original indices
                assert exists|j: int| k_int <= j < s.len() && s[j] == z;
            }
        };
        
        // The subrange equality follows from the loop invariant
        assert(s == s.subrange(0, k_int) + s.subrange(k_int, s.len() as int));
    }
    
    k_int
}

fn Sort(m: Seq<int>) -> (r: Seq<int>)
    ensures r.len() == m.len()
    ensures forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q]
    ensures multiset(r) =~= multiset(m)
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
        invariant multiset(result) =~= multiset(m.subrange(0, i as int))
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
            // Length properties
            assert(result.len() == old_len + 1);
            assert(result.len() == i + 1);
            
            // Prove sorted property by cases
            assert forall|p: int, q: int| 0 <= p < q < result.len() implies result[p] <= result[q] by {
                if 0 <= p < q < result.len() {
                    let left_part = old_result.subrange(0, ji);
                    let right_part = old_result.subrange(ji, old_len as int);
                    
                    if q < ji {
                        // Both in left part
                        assert(result[p] == old_result[p]);
                        assert(result[q] == old_result[q]);
                        assert(old_result[p] <= old_result[q]);
                    } else if p < ji && q == ji {
                        // p in left part, q is inserted value
                        assert(result[p] == old_result[p]);
                        assert(result[q] == value);
                        assert(old_result[p] <= value);
                    } else if p < ji && q > ji {
                        // p in left part, q in right part (shifted)
                        assert(result[p] == old_result[p]);
                        assert(result[q] == old_result[q - 1]);
                        assert(old_result[p] <= value);
                        if ji < old_len {
                            assert(value <= old_result[ji]);
                            assert(old_result[ji] <= old_result[q - 1]);
                        }
                    } else if p == ji && q > ji {
                        // p is inserted value, q in right part
                        assert(result[p] == value);
                        assert(result[q] == old_result[q - 1]);
                        if ji < old_len {
                            assert(value <= old_result[ji]);
                            assert(old_result[ji] <= old_result[q - 1]);
                        }
                    } else {
                        // Both in right part (shifted)
                        assert(result[p] == old_result[p - 1]);
                        assert(result[q] == old_result[q - 1]);
                        assert(old_result[p - 1] <= old_result[q - 1]);
                    }
                }
            };
            
            // Multiset preservation
            // The key insight: inserting into a sequence preserves multiset + new element
            assert(multiset(m.subrange(0, ii + 1)) =~= multiset(m.subrange(0, ii)).insert(value));
            assert(multiset(old_result) =~= multiset(m.subrange(0, ii)));
            assert(value == m[ii]);
            
            // Prove that the new result has the right multiset
            let left = result.subrange(0, ji);
            let middle = seq![value];
            let right = result.subrange(ji + 1, result.len() as int);
            
            assert(left == old_result.subrange(0, ji));
            assert(right == old_result.subrange(ji, old_len as int));
            assert(multiset(result) =~= multiset(left).add(multiset(middle)).add(multiset(right)));
            assert(multiset(result) =~= multiset(old_result).insert(value));
            assert(multiset(result) =~= multiset(m.subrange(0, ii + 1)));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == m.len());
        assert(result.len() == m.len());
        assert(multiset(result) =~= multiset(m.subrange(0, m.len() as int)));
        // Use the fact that subrange(0, len) == original sequence
        assert(m.subrange(0, m.len() as int) =~= m);
    }
    
    result
}

}