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
    lemma_mod_basics(i - n + len, 0, len);
    lemma_mod_basics(split_point + i, 0, len);
    
    if i < len - split_point {
        // In right part
        assert(split_point + i < len);
        assert((split_point + i) % len == split_point + i);
        
        // Show split_point + i == (i - n + len) % len
        let target = i - n + len;
        assert(split_point == len - effective_n);
        assert(effective_n == n % len);
        
        // Key insight: split_point + i = len - (n % len) + i
        calc! {
            (split_point + i)
            == (len - effective_n + i) // def of split_point
            == (len - (n % len) + i) // def of effective_n
        }
        
        // Show this equals (i - n + len) % len
        calc! {
            (i - n + len) % len
            == (i + len - n) % len // rearrange
            == (i + len - (n % len + (n / len) * len)) % len // n = n%len + (n/len)*len
            == (i + len - n % len - (n / len) * len) % len // distribute
            == (i + len - n % len) % len // modular arithmetic
            == (len - n % len + i) % len // rearrange
            == (len - effective_n + i) % len // def of effective_n
            == (split_point + i) % len // def of split_point
            == split_point + i // since split_point + i < len
        }
    } else {
        // In left part
        let left_idx = i - (len - split_point);
        assert(0 <= left_idx < split_point);
        assert(left_idx % len == left_idx);
        
        calc! {
            left_idx
            == i - (len - split_point) // def
            == i - len + split_point // simplify
            == i - len + (len - effective_n) // def of split_point
            == i - effective_n // simplify
        }
        
        // Show i - effective_n == (i - n + len) % len
        calc! {
            (i - n + len) % len
            == (i - (n % len + (n / len) * len) + len) % len // n = n%len + (n/len)*len
            == (i - n % len + len - (n / len) * len) % len // rearrange
            == (i - n % len) % len // modular arithmetic
            == (i - effective_n) % len // def of effective_n
            == i - effective_n // since 0 <= i - effective_n < len
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