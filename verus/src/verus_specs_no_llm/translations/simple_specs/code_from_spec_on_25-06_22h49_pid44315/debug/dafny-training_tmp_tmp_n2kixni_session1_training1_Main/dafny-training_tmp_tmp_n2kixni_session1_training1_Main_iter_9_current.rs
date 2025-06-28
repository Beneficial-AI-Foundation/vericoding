use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a.spec_index(j) <= a.spec_index(k)
}

fn find(a: Seq<int>, key: int) -> (index: int)
    requires sorted(a)
    ensures 
        -1 <= index < a.len(),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != key),
        index >= 0 ==> a.spec_index(index) == key
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut left: int = 0;
    let mut right: int = a.len() as int - 1;
    
    while left <= right
        invariant
            0 <= left <= a.len(),
            -1 <= right < a.len(),
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < key,
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > key
    {
        let mid = left + (right - left) / 2;
        
        assert(0 <= mid < a.len()) by {
            assert(left <= right);
            assert(left >= 0);
            assert(right < a.len());
            assert(mid >= left);
            assert(mid <= right);
        };
        
        if a.spec_index(mid) < key {
            left = mid + 1;
        } else if a.spec_index(mid) > key {
            right = mid - 1;
        } else {
            return mid;
        }
    }
    
    // At this point, left > right, so the key is not in the array
    assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != key) by {
        assert(left > right);
        // Every index is either < left or > right
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right));
        // Elements < left are < key, elements > right are > key
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < key);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > key);
    };
    
    -1
}

spec fn is_palindrome_spec(a: Seq<char>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) == a.spec_index(a.len() - 1 - i)
}

fn isPalindrome(a: Seq<char>) -> (b: bool)
    requires true
    ensures b == is_palindrome_spec(a)
{
    if a.len() == 0 {
        return true;
    }
    
    let mut i: int = 0;
    let mut j: int = a.len() as int - 1;
    
    while i < j
        invariant
            0 <= i <= a.len(),
            -1 <= j < a.len(),
            i + j == a.len() as int - 1,
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k),
            forall|k: int| j < k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)
    {
        if a.spec_index(i) != a.spec_index(j) {
            // Prove that the palindrome property is violated
            assert(!is_palindrome_spec(a)) by {
                assert(a.spec_index(i) != a.spec_index(j));
                assert(j == a.len() - 1 - i);
                assert(a.spec_index(i) != a.spec_index(a.len() - 1 - i));
            };
            return false;
        }
        
        i = i + 1;
        j = j - 1;
    }
    
    // Prove that all elements satisfy the palindrome property
    assert(is_palindrome_spec(a)) by {
        // Split the proof into cases
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)) by {
            // Elements we've already checked (k < final i)
            assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k));
            // Elements we've already checked (k > final j) 
            assert(forall|k: int| j < k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k));
            
            // At loop exit, i >= j, and i + j == a.len() - 1
            assert(i >= j);
            assert(i + j == a.len() - 1);
            
            // For any remaining elements in the middle
            assert(forall|k: int| j < k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)) by {
                // When i >= j after loop, the range j < k < i contains at most the middle element(s)
                // Since i + j == a.len() - 1, if j < k < i, then k is close to the middle
                // and its mirror is also close to the middle
                assert(forall|k: int| j < k < i ==> {
                    let mirror = a.len() - 1 - k;
                    // Since i + j == a.len() - 1 and j < k < i, 
                    // we have j < mirror < i as well
                    j < mirror < i
                });
            };
        };
    };
    
    true
}

}