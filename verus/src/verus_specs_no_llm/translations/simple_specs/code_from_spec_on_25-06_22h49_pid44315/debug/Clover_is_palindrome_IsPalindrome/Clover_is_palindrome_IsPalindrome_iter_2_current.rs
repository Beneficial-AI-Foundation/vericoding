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
        // We've checked all pairs (j, len-j-1) for j in [0, len/2)
        assert(forall j: int :: 0 <= j < len / 2 ==> x.spec_index(j) == x.spec_index(len - j - 1));
        
        // For any j in [len/2, len), its mirror len-j-1 is in [0, len/2)
        // and we've already verified that x[len-j-1] == x[len-(len-j-1)-1] = x[j]
        assert(forall j: int :: len / 2 <= j < len ==> {
            let mirror = len - j - 1;
            &&& 0 <= mirror < len / 2
            &&& x.spec_index(mirror) == x.spec_index(len - mirror - 1)
            &&& len - mirror - 1 == j
        });
        
        // Handle the middle element case when len is odd
        if len % 2 == 1 {
            let mid = len / 2;
            assert(x.spec_index(mid) == x.spec_index(len - mid - 1)) by {
                assert(len - mid - 1 == mid);
            }
        }
    }
    
    return true;
}

}