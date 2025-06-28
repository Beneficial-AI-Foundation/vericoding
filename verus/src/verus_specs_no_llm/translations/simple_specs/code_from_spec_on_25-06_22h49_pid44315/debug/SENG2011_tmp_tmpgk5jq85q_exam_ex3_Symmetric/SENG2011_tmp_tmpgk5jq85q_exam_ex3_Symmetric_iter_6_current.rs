use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Symmetric(a: Vec<int>) -> (flag: bool)
    ensures
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> a.spec_index(x) == a.spec_index(a.len() - x - 1),
        flag == false ==> exists|x: int| 0 <= x < a.len() && a.spec_index(x) != a.spec_index(a.len() - x - 1)
{
    let len = a.len();
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(len as int - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(exists|x: int| 0 <= x < len && a.spec_index(x) != a.spec_index(len as int - x - 1)) by {
                assert(0 <= i < len);
                assert(i as int < len as int);
                assert(a.spec_index(i as int) != a.spec_index(len as int - (i as int) - 1));
            }
            return false;
        }
        i += 1;
    }
    
    // Prove that the entire array is symmetric
    assert(forall|x: int| 0 <= x < len ==> a.spec_index(x) == a.spec_index(len as int - x - 1)) by {
        forall|x: int| 0 <= x < len implies {
            if x < (len as int) / 2 {
                // x is in the first half, we already proved this in the loop
                assert(x < i as int);
                assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
            } else if x == (len as int) / 2 && len % 2 == 1 {
                // This is the middle element for odd-length arrays
                assert(len as int - x - 1 == x);
                assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
            } else {
                // x is in the second half
                let mirror = len as int - x - 1;
                assert(mirror >= 0);
                assert(mirror < len as int);
                assert(mirror < (len as int) / 2);
                assert(mirror < i as int);
                // We proved in the loop that a[mirror] == a[len - mirror - 1]
                assert(a.spec_index(mirror) == a.spec_index(len as int - mirror - 1));
                // And len - mirror - 1 == x
                assert(len as int - mirror - 1 == len as int - (len as int - x - 1) - 1);
                assert(len as int - (len as int - x - 1) - 1 == x);
                assert(a.spec_index(x) == a.spec_index(len as int - x - 1));
            }
        }
    };
    
    true
}

}