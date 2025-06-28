use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires
        a.len() == b.len()
    ensures
        result <==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) > b.spec_index(i),
        !result <==> exists i :: 0 <= i < a.len() && a.spec_index(i) <= b.spec_index(i)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall j :: 0 <= j < i ==> a.spec_index(j) > b.spec_index(j)
    {
        if a.spec_index(i as int) <= b.spec_index(i as int) {
            assert(a.spec_index(i as int) <= b.spec_index(i as int));
            assert(exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k)) by {
                assert(0 <= i < a.len());
                assert(a.spec_index(i as int) <= b.spec_index(i as int));
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j)) by {
        assert(forall j :: 0 <= j < i ==> a.spec_index(j) > b.spec_index(j));
        assert(i == a.len());
    }
    
    return true;
}

}