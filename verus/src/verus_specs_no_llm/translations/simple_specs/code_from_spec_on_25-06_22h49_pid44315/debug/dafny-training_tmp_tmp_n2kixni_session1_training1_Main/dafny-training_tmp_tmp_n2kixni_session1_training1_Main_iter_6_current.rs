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
            left <= right + 1,
            forall|i: int| 0 <= i < left ==> a.spec_index(i) < key,
            forall|i: int| right < i < a.len() ==> a.spec_index(i) > key
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid <= right);
        assert(0 <= mid < a.len());
        
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
        // All indices are covered by the two ranges from the invariant
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right)) by {
            assert(left <= a.len());
            assert(right >= -1);
        };
        // Use the invariant properties
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < key);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > key);
        // Since left > right and all elements less than left are < key 
        // and all elements > right are > key, no element can equal key
        assert(forall|i: int| 0 <= i < a.len() ==> {
            if i < left {
                a.spec_index(i) < key
            } else {
                i > right && a.spec_index(i) > key
            }
        });
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
            assert(!is_palindrome_spec(a)) by {
                assert(j == a.len() - 1 - i);
                assert(a.spec_index(i) != a.spec_index(a.len() - 1 - i));
            };
            return false;
        }
        
        // After checking that elements at i and j match, update invariant
        assert(a.spec_index(i) == a.spec_index(j));
        assert(j == a.len() - 1 - i);
        assert(a.spec_index(i) == a.spec_index(a.len() - 1 - i));
        
        i = i + 1;
        j = j - 1;
    }
    
    // Prove that all elements satisfy the palindrome property
    assert(is_palindrome_spec(a)) by {
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)) by {
            // At this point i >= j, and we have i + j + 1 == a.len()
            // All positions 0..i are verified by the first part of invariant
            // All positions j+1..a.len() are verified by the second part of invariant
            // The middle position (if any) is automatically palindromic
            assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k));
            assert(forall|k: int| j < k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k));
            
            // For any k in the remaining range [i, j], show it satisfies palindrome property
            assert(forall|k: int| i <= k <= j ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)) by {
                // Since i >= j after the loop, this range is at most one element
                // For any k in this range, a.len() - 1 - k is also in this range
                if i == j {
                    // Single middle element - automatically palindromic with itself
                    assert(i == j && i == a.len() - 1 - i);
                }
            };
        };
    };
    
    true
}

}