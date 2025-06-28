use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPalindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall i: int :: 0 <= i < x.len() ==> x.spec_index(i) == x.spec_index(x.len() - i - 1))
{
    let len = x.len();
    
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let half_len = (len / 2) as usize;
    
    while i < half_len
        invariant 
            0 <= i <= half_len,
            half_len == len / 2,
            len == x.len(),
            forall j: int :: 0 <= j < i ==> x.spec_index(j) == x.spec_index(len - j - 1)
    {
        if x.spec_index(i as int) != x.spec_index(len - (i as int) - 1) {
            // Found a mismatch, so it's not a palindrome
            assert(!(forall k: int :: 0 <= k < len ==> x.spec_index(k) == x.spec_index(len - k - 1))) by {
                assert(0 <= i < len);
                assert(x.spec_index(i as int) != x.spec_index(len - (i as int) - 1));
            }
            return false;
        }
        i = i + 1;
    }
    
    // After the loop, we've verified all pairs up to the middle
    assert(i == half_len);
    assert(forall j: int :: 0 <= j < len / 2 ==> x.spec_index(j) == x.spec_index(len - j - 1));
    
    // Prove the full palindrome property
    assert(forall k: int :: 0 <= k < len ==> x.spec_index(k) == x.spec_index(len - k - 1)) by {
        assert forall k: int where 0 <= k < len implies x.spec_index(k) == x.spec_index(len - k - 1) by {
            let mirror_k = len - k - 1;
            assert(0 <= mirror_k < len);
            
            if k < len / 2 {
                // k is in the first half, use our loop invariant
                assert(x.spec_index(k) == x.spec_index(len - k - 1));
            } else if k >= (len + 1) / 2 {
                // k is in the second half, mirror_k is in the first half
                assert(mirror_k < len / 2);
                assert(x.spec_index(mirror_k) == x.spec_index(len - mirror_k - 1));
                assert(len - mirror_k - 1 == k);
                assert(x.spec_index(k) == x.spec_index(mirror_k));
            } else {
                // k is the middle element (only possible when len is odd)
                assert(len % 2 == 1);
                assert(k == len / 2);
                assert(mirror_k == len / 2);
                assert(k == mirror_k);
                assert(x.spec_index(k) == x.spec_index(mirror_k));
            }
        }
    };
    
    true
}

}