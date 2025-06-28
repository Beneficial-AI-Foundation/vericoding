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
            assert(!(forall k: int :: 0 <= k < len ==> x.spec_index(k) == x.spec_index(len - k - 1)));
            return false;
        }
        i = i + 1;
    }
    
    // After the loop, we've verified all pairs up to the middle
    assert(forall j: int :: 0 <= j < len / 2 ==> x.spec_index(j) == x.spec_index(len - j - 1));
    
    // Now prove that this implies the full palindrome property
    assert forall k: int where 0 <= k < len implies x.spec_index(k) == x.spec_index(len - k - 1) by {
        let mirror_k = len - k - 1;
        if k < len / 2 {
            // We proved this case in the loop
            assert(x.spec_index(k) == x.spec_index(mirror_k));
        } else if k >= (len + 1) / 2 {
            // Use symmetry: the mirror position was already checked
            let mirror_pos = len - k - 1;
            assert(mirror_pos >= 0 && mirror_pos < len / 2);
            assert(x.spec_index(mirror_pos) == x.spec_index(len - mirror_pos - 1));
            assert(len - mirror_pos - 1 == k);
            assert(x.spec_index(k) == x.spec_index(mirror_k));
        } else {
            // Middle element case for odd length
            assert(k == len / 2);
            assert(mirror_k == len - len / 2 - 1);
            if len % 2 == 1 {
                assert(mirror_k == len / 2);
                assert(k == mirror_k);
            }
        }
    };
    
    true
}

}