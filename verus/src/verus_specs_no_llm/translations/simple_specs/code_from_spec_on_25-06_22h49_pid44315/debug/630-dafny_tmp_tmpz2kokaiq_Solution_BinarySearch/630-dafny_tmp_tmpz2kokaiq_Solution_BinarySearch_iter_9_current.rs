use builtin::*;
use builtin_macros::*;

verus! {

spec fn sorted(a: Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
}

fn main() {
}

fn BinarySearch(a: Vec<int>, x: int) -> (index: int)
    requires
        sorted(a)
    ensures
        0 <= index < a.len() ==> a.spec_index(index) == x,
        index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x
{
    if a.len() == 0 {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a.spec_index(i) < x,
            forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x,
            sorted(a)
        decreases (high - low) as int
    {
        let mid = low + (high - low) / 2;
        
        if a[mid as int] == x {
            return mid as int;
        } else if a[mid as int] < x {
            proof {
                assert(a.spec_index(mid as int) < x);
                // Use sortedness to prove that all elements <= mid are < x
                assert(forall|i: int| 0 <= i <= mid ==> {
                    &&& i < a.len()
                    &&& a.spec_index(i) <= a.spec_index(mid as int)
                    &&& a.spec_index(i) < x
                }) by {
                    assert(sorted(a));
                    assert(mid < a.len());
                    assert(forall|i: int| 0 <= i <= mid < a.len() ==> a.spec_index(i) <= a.spec_index(mid as int));
                };
            }
            low = mid + 1;
        } else {
            proof {
                assert(a.spec_index(mid as int) > x);
                // Use sortedness to prove that all elements >= mid are > x
                assert(forall|i: int| mid <= i < a.len() ==> {
                    &&& a.spec_index(mid as int) <= a.spec_index(i)
                    &&& a.spec_index(i) > x
                }) by {
                    assert(sorted(a));
                    assert(mid < a.len());
                    assert(forall|i: int| mid <= i < a.len() ==> a.spec_index(mid as int) <= a.spec_index(i));
                };
            }
            high = mid;
        }
    }
    
    proof {
        assert(low == high);
        assert(forall|i: int| 0 <= i < low ==> a.spec_index(i) < x);
        assert(forall|i: int| high <= i < a.len() ==> a.spec_index(i) > x);
        assert(forall|i: int| 0 <= i < a.len() ==> {
            ||| i < low as int
            ||| i >= high as int
        });
        assert(forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x) by {
            assert(forall|i: int| 0 <= i < a.len() ==> {
                if i < low as int {
                    a.spec_index(i) < x
                } else {
                    i >= high as int && a.spec_index(i) > x
                }
            });
        };
    }
    
    return -1;
}

}