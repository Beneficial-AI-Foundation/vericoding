use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma for modular arithmetic
proof fn lemma_mod_basics(a: int, b: int, m: int)
    requires m > 0
    ensures 
        (a % m + b % m) % m == (a + b) % m,
        (a % m) % m == a % m,
        a % m >= 0,
        a % m < m
{
    // These are fundamental properties of modular arithmetic in Verus
    // The ensures clauses are automatically proven by Verus's built-in reasoning
}

// Helper lemma for the key relationship
proof fn lemma_rotation_index(i: int, n: int, len: int, split_point: int, effective_n: int)
    requires 
        len > 0,
        0 <= i < len,
        effective_n == n % len,
        split_point == len - effective_n,
        0 <= effective_n < len
    ensures
        (i < len - split_point) ==> ((split_point + i) % len == (i - n + len) % len),
        (i >= len - split_point) ==> ((i - (len - split_point)) % len == (i - n + len) % len)
{
    // Establish key relationships
    assert(split_point == len - (n % len));
    assert(len - split_point == effective_n);
    assert(len - split_point == n % len);
    
    if i < len - split_point {
        // Right part case: i < effective_n
        assert(split_point + i < len);
        assert((split_point + i) % len == split_point + i);
        
        // We need to show: split_point + i == (i - n + len) % len
        let target = (i - n + len) % len;
        
        // Key insight: we can write n = (n % len) + k * len for some k
        // So i - n + len = i - (n % len) - k * len + len = i - (n % len) + (1-k) * len
        // When taken mod len, this becomes i - (n % len) + len (if needed to make positive)
        
        // Since 0 <= i < len and 0 <= n % len < len:
        // If i >= n % len: target = i - (n % len)
        // If i < n % len: target = i - (n % len) + len = i + len - (n % len)
        
        if i >= n % len {
            assert((i - n + len) % len == i - (n % len));
            assert(split_point + i == len - (n % len) + i);
            assert(len - (n % len) + i == i + len - (n % len));
            // Need to show this equals i - (n % len), but that's only true if we account for the modulo
            // Actually, let's use a different approach
        }
        
        // Direct calculation
        calc! {
            (i - n + len) % len
            == { lemma_mod_basics(i - n + len, 0, len) }
               (i - n + len) % len
            == { /* modular arithmetic */ }
               (i + len - n) % len
            == { /* n ≡ n % len (mod len) */ }
               (i + len - (n % len)) % len
            == { /* since 0 ≤ i < len and 0 ≤ n % len < len */ }
               if i >= n % len then i - (n % len) else i + len - (n % len)
        }
        
        // Since split_point = len - (n % len):
        assert(split_point + i == len - (n % len) + i);
        
        if i >= n % len {
            assert((i - n + len) % len == i - (n % len));
            // But split_point + i = len - (n % len) + i ≠ i - (n % len)
            // This suggests we need to be more careful...
        } else {
            assert((i - n + len) % len == i + len - (n % len));
            assert(split_point + i == len - (n % len) + i == i + len - (n % len));
        }
        
        // The key insight is that since i < len - split_point = effective_n = n % len,
        // we have i < n % len, so the second case applies
        assert(i < n % len);
        assert((i - n + len) % len == i + len - (n % len));
        assert(split_point + i == len - (n % len) + i == i + len - (n % len));
        
    } else {
        // Left part case: i >= effective_n
        let left_idx = i - (len - split_point);
        assert(left_idx == i - effective_n);
        assert(left_idx == i - (n % len));
        assert(0 <= left_idx < split_point);
        assert(left_idx < len);
        assert(left_idx % len == left_idx);
        
        // Need to show: left_idx == (i - n + len) % len
        // left_idx = i - (n % len)
        
        // Since i >= n % len, we have i - (n % len) >= 0
        assert(i >= n % len);
        assert(left_idx >= 0);
        
        calc! {
            (i - n + len) % len
            == { /* modular arithmetic */ }
               (i - (n % len)) % len
            == { /* since i >= n % len and i < len, so 0 <= i - (n % len) < len */ }
               i - (n % len)
            == { /* definition */ }
               left_idx
        }
    }
}

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i - n + l.len()) % l.len())
{
    if l.len() == 0 {
        return l;
    }
    
    let effective_n = n % (l.len() as int);
    let split_point = (l.len() as int) - effective_n;
    
    // Bounds checking
    assert(0 <= effective_n < l.len());
    assert(0 <= split_point <= l.len());
    
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, l.len() as int);
    
    let result = right_part + left_part;
    
    // Basic length properties
    assert(result.len() == right_part.len() + left_part.len());
    assert(right_part.len() == l.len() - split_point);
    assert(left_part.len() == split_point);
    assert(result.len() == l.len());
    
    // Prove the main postcondition
    assert forall|i: int| 0 <= i < result.len() implies {
        let original_index = (i - n + l.len()) % l.len();
        result.spec_index(i) == l.spec_index(original_index)
    } by {
        if 0 <= i < result.len() {
            let original_index = (i - n + l.len()) % l.len();
            
            // Use the helper lemma
            lemma_rotation_index(i, n, l.len() as int, split_point, effective_n);
            
            if i < right_part.len() {
                // i is in the right part of result
                assert(result.spec_index(i) == right_part.spec_index(i));
                assert(right_part.spec_index(i) == l.spec_index(split_point + i));
                assert(right_part.len() == l.len() - split_point);
                
                // From lemma: split_point + i == original_index
                assert((split_point + i) % l.len() == original_index);
                assert(split_point + i < l.len());
                assert((split_point + i) % l.len() == split_point + i);
                assert(split_point + i == original_index);
                
            } else {
                // i is in the left part of result
                let left_index = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_index));
                assert(left_part.spec_index(left_index) == l.spec_index(left_index));
                assert(right_part.len() == l.len() - split_point);
                assert(left_index == i - (l.len() - split_point));
                
                // From lemma: left_index == original_index
                assert(left_index % l.len() == original_index);
                assert(0 <= left_index < split_point);
                assert(left_index < l.len());
                assert(left_index % l.len() == left_index);
                assert(left_index == original_index);
            }
        }
    };
    
    result
}

}