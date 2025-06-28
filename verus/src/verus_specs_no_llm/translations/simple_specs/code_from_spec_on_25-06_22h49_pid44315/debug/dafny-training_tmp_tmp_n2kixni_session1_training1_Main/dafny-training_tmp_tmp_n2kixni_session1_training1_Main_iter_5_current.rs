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
        assert(forall|i: int| 0 <= i < a.len() ==> (i < left || i > right));
        assert(forall|i: int| 0 <= i < left ==> a.spec_index(i) < key);
        assert(forall|i: int| right < i < a.len() ==> a.spec_index(i) > key);
    }
    
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
            0 <= i,
            j < a.len(),
            i + j == a.len() as int - 1,
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)
    {
        if a.spec_index(i) != a.spec_index(j) {
            assert(!is_palindrome_spec(a)) by {
                assert(j == a.len() - 1 - i);
                assert(a.spec_index(i) != a.spec_index(a.len() - 1 - i));
            }
            return false;
        }
        i = i + 1;
        j = j - 1;
    }
    
    // Prove that all elements satisfy the palindrome property
    assert(is_palindrome_spec(a)) by {
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k)) by {
            // For any index k, either:
            // 1. k < i: covered by invariant
            // 2. k >= i: then a.len() - 1 - k <= j < i, so it's the symmetric case
            assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(a.len() - 1 - k));
            // For k >= i, we use symmetry
            assert(forall|k: int| i <= k < a.len() ==> {
                let sym_k = a.len() - 1 - k;
                sym_k < i && a.spec_index(sym_k) == a.spec_index(a.len() - 1 - sym_k)
            });
        }
    }
    
    true
}

}