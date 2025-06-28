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
    let mut i: usize = 0;
    let len = a.len();
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|x: int| 0 <= x < i ==> a.spec_index(x) == a.spec_index(len - x - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(a.spec_index(i as int) != a.spec_index(len - (i as int) - 1));
            return false;
        }
        i += 1;
    }
    
    assert(forall|x: int| 0 <= x < len ==> a.spec_index(x) == a.spec_index(len - x - 1)) by {
        assert(forall|x: int| 0 <= x < len / 2 ==> a.spec_index(x) == a.spec_index(len - x - 1));
        assert(forall|x: int| len / 2 <= x < len ==> {
            let mirror = len - x - 1;
            &&& 0 <= mirror < len / 2
            &&& a.spec_index(mirror) == a.spec_index(len - mirror - 1)
            &&& len - mirror - 1 == x
        });
    };
    
    true
}

}