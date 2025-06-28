use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma for modular arithmetic properties
proof fn lemma_mod_basics(a: int, b: int, m: int)
    requires m > 0
    ensures 
        (a % m + b % m) % m == (a + b) % m,
        (a % m) % m == a % m,
        a % m >= 0,
        a % m < m
{
    assert(a % m >= 0 && a % m < m);
    assert(b % m >= 0 && b % m < m);
    assert((a % m) % m == a % m);
    assert((a % m + b % m) % m == (a + b) % m);
}

// Helper lemma for handling modular arithmetic with addition of multiples
proof fn lemma_mod_add_multiple(a: int, k: int, m: int)
    requires m > 0
    ensures (a + k * m) % m == a % m
{
    assert((a + k * m) % m == a % m);
}

// Helper lemma for modular arithmetic equivalence
proof fn lemma_mod_equiv(a: int, b: int, m: int)
    requires m > 0, a % m == b % m
    ensures a % m == b % m
{
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
    
    let len = l.len();
    let len_int = len as int;
    let effective_n = n % len_int;
    let split_point = len_int - effective_n;
    
    // Create the rotated sequence by concatenating the two parts
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, len_int);
    let result = right_part + left_part;
    
    // Prove the postcondition
    assert forall|i: int| 0 <= i < result.len() implies {
        let target_index = (i - n + len_int) % len_int;
        result.spec_index(i) == l.spec_index(target_index)
    } by {
        if 0 <= i < result.len() {
            let target_index = (i - n + len_int) % len_int;
            
            // target_index is always in valid range
            assert(0 <= target_index < len_int);
            
            if i < right_part.len() {
                // Case 1: i indexes into the right_part of result
                let orig_right_idx = split_point + i;
                assert(result.spec_index(i) == right_part.spec_index(i));
                assert(right_part.spec_index(i) == l.spec_index(orig_right_idx));
                
                // Prove that target_index == orig_right_idx
                // We need to show (i - n + len_int) % len_int == orig_right_idx
                lemma_mod_add_multiple(i - effective_n, 1, len_int);
                assert(effective_n == n % len_int);
                assert((i - n + len_int) % len_int == (i - effective_n + len_int) % len_int);
                assert(split_point == len_int - effective_n);
                assert(orig_right_idx == len_int - effective_n + i);
                
                // Since i < right_part.len() = len_int - split_point = effective_n
                assert(i < effective_n);
                assert(i - effective_n < 0);
                assert(i - effective_n + len_int >= 0);
                assert(i - effective_n + len_int < len_int);
                assert((i - effective_n + len_int) % len_int == i - effective_n + len_int);
                assert(i - effective_n + len_int == orig_right_idx);
                assert(target_index == orig_right_idx);
                
            } else {
                // Case 2: i indexes into the left_part of result
                let left_idx = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_idx));
                assert(left_part.spec_index(left_idx) == l.spec_index(left_idx));
                
                // Prove that target_index == left_idx
                assert(right_part.len() == len_int - split_point);
                assert(right_part.len() == effective_n);
                assert(left_idx == i - effective_n);
                
                // Since i >= right_part.len() = effective_n
                assert(i >= effective_n);
                assert(left_idx >= 0);
                assert(left_idx < left_part.len());
                assert(left_part.len() == split_point);
                assert(left_idx < len_int);
                
                lemma_mod_add_multiple(i - effective_n, 1, len_int);
                assert((i - n + len_int) % len_int == (i - effective_n + len_int) % len_int);
                assert(i - effective_n >= 0);
                assert(i - effective_n < len_int);
                assert((i - effective_n + len_int) % len_int == (i - effective_n) % len_int);
                assert((i - effective_n) % len_int == i - effective_n);
                assert(target_index == left_idx);
            }
            
            assert(result.spec_index(i) == l.spec_index(target_index));
        }
    };
    
    result
}

}