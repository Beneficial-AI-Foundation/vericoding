use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxLengthList(lists: Seq<Seq<int>>) -> (maxList: Seq<int>)
    requires
        lists.len() > 0
    ensures
        forall|l: Seq<int>| lists.contains(l) ==> l.len() <= maxList.len(),
        lists.contains(maxList)
{
    let mut maxList = lists[0];
    let mut i = 1;
    
    while i < lists.len()
        invariant
            0 <= i <= lists.len(),
            lists.contains(maxList),
            forall|j: int| 0 <= j < i ==> lists[j].len() <= maxList.len()
    {
        if lists[i as int].len() > maxList.len() {
            maxList = lists[i as int];
        }
        i = i + 1;
    }
    
    // Prove the postcondition
    assert forall|l: Seq<int>| lists.contains(l) implies l.len() <= maxList.len() by {
        // For any list l that is contained in lists
        if lists.contains(l) {
            // There must be some index where l appears
            let k = choose|k: int| 0 <= k < lists.len() && lists[k] == l;
            
            // After loop termination, i == lists.len()
            assert(i == lists.len());
            assert(0 <= k < lists.len());
            assert(k < i);
            
            // From the loop invariant, we know that all elements with index < i
            // have length <= maxList.len()
            assert(lists[k].len() <= maxList.len());
            assert(l.len() <= maxList.len());
        }
    };
    
    maxList
}

}