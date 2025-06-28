use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < list.len() && sub == list.spec_index(i))
{
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall j: int :: 0 <= j < i ==> sub != list.spec_index(j),
    {
        if sub == list.spec_index(i as int) {
            assert(exists k :: 0 <= k < list.len() && sub == list.spec_index(k)) by {
                assert(0 <= i as int < list.len());
                assert(sub == list.spec_index(i as int));
            };
            return true;
        }
        i = i + 1;
    }
    
    assert(forall j :: 0 <= j < list.len() ==> sub != list.spec_index(j)) by {
        assert(i as int == list.len());
        assert(forall j: int :: 0 <= j < i ==> sub != list.spec_index(j));
    };
    
    return false;
}

}