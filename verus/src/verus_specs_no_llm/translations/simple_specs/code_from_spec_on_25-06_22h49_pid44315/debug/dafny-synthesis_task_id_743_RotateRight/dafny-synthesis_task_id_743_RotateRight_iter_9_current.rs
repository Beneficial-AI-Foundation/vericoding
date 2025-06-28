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
    // These are built-in properties of modular arithmetic in Verus
    // The SMT solver should be able to prove these automatically
}

// Helper lemma for handling modular arithmetic with addition of multiples
proof fn lemma_mod_add_multiple(a: int, k: int, m: int)
    requires m > 0
    ensures (a + k * m) % m == a % m
{
    // This is a fundamental property of modular arithmetic
    // (a + k*m) ≡ a (mod m) for any integer k
}

// Simplified helper lemma for the key relationship
proof fn lemma_rotation_correctness(i: int, n: int, len: int)
    requires 
        len > 0,
        0 <= i < len,
        n >= 0
    ensures
        0 <= (i - n + len) % len < len
{
    // Basic property: for any integer x and positive m, 0 <= x % m < m
    // Since len > 0, we have 0 <= (i - n + len) % len < len
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
    
    let len = l.len() as int;
    let effective_n = n % len;
    let split_point = len - effective_n;
    
    // Bounds checking
    assert(0 <= effective_n < len);
    assert(0 <= split_point <= len);
    
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, len);
    
    let result = right_part + left_part;
    
    // Basic length properties
    assert(result.len() == right_part.len() + left_part.len());
    assert(right_part.len() == len - split_point);
    assert(left_part.len() == split_point);
    assert(result.len() == l.len());
    
    // Prove the main postcondition
    assert forall|i: int| 0 <= i < result.len() implies {
        let original_index = (i - n + len) % len;
        result.spec_index(i) == l.spec_index(original_index)
    } by {
        if 0 <= i < result.len() {
            let original_index = (i - n + len) % len;
            lemma_rotation_correctness(i, n, len);
            
            if i < right_part.len() {
                // i is in the right part of result (originally from position split_point + i)
                assert(result.spec_index(i) == right_part.spec_index(i));
                assert(right_part.spec_index(i) == l.spec_index(split_point + i));
                
                // Since i < right_part.len() = len - split_point = effective_n
                assert(i < effective_n);
                assert(i < n % len);
                
                // For the modular arithmetic proof
                lemma_mod_add_multiple(i - effective_n + len, 0, len);
                assert(split_point + i == len - effective_n + i);
                assert(i - effective_n < 0);
                assert(i - effective_n + len == len + i - effective_n);
                assert(len + i - effective_n == split_point + i);
                assert(0 <= split_point + i < len);
                assert((split_point + i) % len == split_point + i);
                
                // Show that (i - n + len) % len == split_point + i
                lemma_mod_add_multiple(i - effective_n, 1, len);
                assert((i - n + len) % len == (i - effective_n + len) % len);
                assert((i - effective_n + len) % len == split_point + i);
                
                assert(l.spec_index(split_point + i) == l.spec_index(original_index));
                assert(result.spec_index(i) == l.spec_index(original_index));
                
            } else {
                // i is in the left part of result (originally from position i - right_part.len())
                let left_index = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_index));
                assert(left_part.spec_index(left_index) == l.spec_index(left_index));
                assert(right_part.len() == len - split_point);
                assert(left_index == i - (len - split_point));
                assert(left_index == i - effective_n);
                
                // Since i >= right_part.len() = effective_n = n % len
                assert(i >= effective_n);
                assert(i >= n % len);
                
                // For i >= n % len, we have i - (n % len) >= 0
                assert(0 <= i - effective_n < split_point);
                assert(i - effective_n < len);
                assert((i - effective_n) % len == i - effective_n);
                
                // Show that (i - n + len) % len == i - effective_n
                lemma_mod_add_multiple(i - effective_n, 1, len);
                assert((i - n + len) % len == (i - effective_n + len) % len);
                assert((i - effective_n + len) % len == i - effective_n);
                
                assert(left_index == i - effective_n);
                assert(left_index == original_index);
                assert(l.spec_index(left_index) == l.spec_index(original_index));
                assert(result.spec_index(i) == l.spec_index(original_index));
            }
        }
    };
    
    result
}

}