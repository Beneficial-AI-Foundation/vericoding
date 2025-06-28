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
    // These are basic properties of modular arithmetic that Verus can prove automatically
}

// Helper lemma for handling modular arithmetic with addition of multiples
proof fn lemma_mod_add_multiple(a: int, k: int, m: int)
    requires m > 0
    ensures (a + k * m) % m == a % m
{
    // This follows from properties of modular arithmetic
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
        (i < len - split_point) ==> ((split_point + i) == (i - n + len) % len),
        (i >= len - split_point) ==> ((i - (len - split_point)) == (i - n + len) % len)
{
    // Key relationships
    assert(split_point == len - (n % len));
    assert(len - split_point == effective_n);
    assert(len - split_point == n % len);
    
    if i < len - split_point {
        // Right part case: i < effective_n = n % len
        assert(i < n % len);
        assert(split_point + i < len);
        
        // We need to show: split_point + i == (i - n + len) % len
        // Since n ≡ effective_n (mod len), we have n = effective_n + k*len for some k
        // So i - n + len = i - (effective_n + k*len) + len = i - effective_n + (1-k)*len
        
        lemma_mod_add_multiple(i - effective_n, 1, len);
        assert((i - effective_n + len) % len == (i - effective_n) % len);
        
        // Since i < effective_n, we have i - effective_n < 0
        // So i - effective_n + len = i + len - effective_n = i + split_point
        assert(i - effective_n + len == i + split_point);
        assert(0 <= i + split_point < len);
        assert((i + split_point) % len == i + split_point);
        assert(split_point + i == (i - n + len) % len);
        
    } else {
        // Left part case: i >= effective_n = n % len
        assert(i >= n % len);
        let left_idx = i - (len - split_point);
        assert(left_idx == i - effective_n);
        
        assert(0 <= left_idx < split_point);
        assert(left_idx < len);
        
        // We need to show: left_idx == (i - n + len) % len
        lemma_mod_add_multiple(i - effective_n, 1, len);
        assert((i - effective_n + len) % len == (i - effective_n) % len);
        
        // Since i >= effective_n, we have i - effective_n >= 0
        // And since i < len, we have i - effective_n < len - effective_n = split_point < len
        assert(0 <= i - effective_n < len);
        assert((i - effective_n) % len == i - effective_n);
        assert(left_idx == i - effective_n);
        assert(left_idx == (i - n + len) % len);
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
                assert(split_point + i == original_index);
                assert(l.spec_index(split_point + i) == l.spec_index(original_index));
                assert(result.spec_index(i) == l.spec_index(original_index));
                
            } else {
                // i is in the left part of result
                let left_index = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_index));
                assert(left_part.spec_index(left_index) == l.spec_index(left_index));
                assert(right_part.len() == l.len() - split_point);
                assert(left_index == i - (l.len() - split_point));
                
                // From lemma: left_index == original_index
                assert(left_index == original_index);
                assert(l.spec_index(left_index) == l.spec_index(original_index));
                assert(result.spec_index(i) == l.spec_index(original_index));
            }
        }
    };
    
    result
}

}