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
            assert(x.spec_index(i as int) != x.spec_index(len - (i as int) - 1));
            assert(0 <= i < len);
            return false;
        }
        i = i + 1;
    }
    
    // After the loop, we've verified all pairs up to the middle
    assert(i == half_len);
    assert(forall j: int :: 0 <= j < len / 2 ==> x.spec_index(j) == x.spec_index(len - j - 1));
    
    // Now prove that this implies the full palindrome property
    assert forall k: int where 0 <= k < len implies x.spec_index(k) == x.spec_index(len - k - 1) by {
        if k < len / 2 {
            // We proved this case in the loop
        } else if k >= len / 2 {
            // Use symmetry: consider the mirror position
            let mirror_pos = len - k - 1;
            assert(mirror_pos >= 0) by {
                assert(k < len);
                assert(len - k - 1 >= 0);
            }
            assert(mirror_pos < len) by {
                assert(k >= 0);
                assert(len - k - 1 < len);
            }
            
            if mirror_pos < len / 2 {
                // The mirror position was already checked in the loop
                assert(x.spec_index(mirror_pos) == x.spec_index(len - mirror_pos - 1));
                assert(len - mirror_pos - 1 == k) by {
                    assert(len - (len - k - 1) - 1 == k);
                }
            } else {
                // mirror_pos >= len / 2, which means k <= len / 2
                // Since we're in the case k >= len / 2, we have k == len / 2
                assert(k == len / 2) by {
                    assert(k >= len / 2);
                    assert(mirror_pos >= len / 2);
                    assert(mirror_pos == len - k - 1);
                    assert(len - k - 1 >= len / 2);
                    assert(k <= len / 2);
                }
                assert(mirror_pos == len / 2) by {
                    assert(mirror_pos == len - k - 1);
                    assert(k == len / 2);
                }
                // When k == len / 2, we have len - k - 1 == len / 2 as well (for odd lengths)
                // or they refer to the same middle element
                assert(k == len - k - 1) by {
                    assert(k == len / 2);
                    assert(len - k - 1 == len - len / 2 - 1);
                    // For this to hold, we need len to be odd, or k to be exactly in the middle
                    if len % 2 == 1 {
                        assert(len / 2 + len / 2 + 1 == len);
                        assert(len - len / 2 - 1 == len / 2);
                    } else {
                        // For even length, k < len / 2 in our loop, so this case doesn't occur
                        assert(false);
                    }
                }
            }
        }
    };
    
    true
}

}