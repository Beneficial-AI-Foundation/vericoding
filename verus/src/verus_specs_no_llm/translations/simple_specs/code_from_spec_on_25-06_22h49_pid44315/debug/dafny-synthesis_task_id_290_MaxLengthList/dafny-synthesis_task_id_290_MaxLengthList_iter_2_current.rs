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
    
    // Proof that maxList satisfies the postcondition
    assert forall|l: Seq<int>| lists.contains(l) implies l.len() <= maxList.len() by {
        // For any sequence l in lists, we need to show l.len() <= maxList.len()
        assert forall|l: Seq<int>| lists.contains(l) implies {
            // l must be at some index in lists
            exists|k: int| 0 <= k < lists.len() && lists[k] == l
        };
        // Since we examined all indices 0..lists.len(), and our invariant ensures
        // that maxList.len() >= lists[j].len() for all j < i, and i == lists.len(),
        // we have maxList.len() >= lists[j].len() for all valid j
    };
    
    maxList
}

}