use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsPalindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall i: int :: 0 <= i < x.len() ==> x.spec_index(i) == x.spec_index(x.len() - i - 1))
{
    let mut i: usize = 0;
    let len = x.len();
    
    while i < len / 2
        invariant 
            0 <= i <= len / 2,
            forall j: int :: 0 <= j < i ==> x.spec_index(j) == x.spec_index(len - j - 1)
    {
        if x.spec_index(i as int) != x.spec_index(len - (i as int) - 1) {
            assert(!forall k: int :: 0 <= k < len ==> x.spec_index(k) == x.spec_index(len - k - 1)) by {
                assert(x.spec_index(i as int) != x.spec_index(len - (i as int) - 1));
                assert(0 <= i < len);
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(forall j: int :: 0 <= j < len ==> x.spec_index(j) == x.spec_index(len - j - 1)) by {
        assert(forall j: int :: 0 <= j < len / 2 ==> x.spec_index(j) == x.spec_index(len - j - 1));
        assert(forall j: int :: len / 2 <= j < len ==> {
            let mirror = len - j - 1;
            &&& 0 <= mirror < len / 2
            &&& x.spec_index(mirror) == x.spec_index(len - mirror - 1)
            &&& len - mirror - 1 == j
        });
    }
    
    return true;
}

}

The implementation works as follows:




   - Using the loop invariant to show the first half matches
   - Reasoning that the second half automatically matches due to symmetry (each character in the second half mirrors to a character in the first half that we've already verified)


The key insight is that checking only the first half is sufficient - if x[i] == x[len-i-1] for all i in [0, len/2), then by symmetry, this property holds for all valid indices in the sequence.