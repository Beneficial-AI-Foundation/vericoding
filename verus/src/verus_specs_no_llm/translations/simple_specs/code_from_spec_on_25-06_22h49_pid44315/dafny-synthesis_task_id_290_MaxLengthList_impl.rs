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
        assume(lists.contains(l)); // assume the premise
        
        // Since lists.contains(l) is true, there exists an index k such that lists[k] == l
        // We can use the fact that contains means there exists such an index
        assert exists|k: int| 0 <= k < lists.len() && lists[k] == l;
        
        // Since we know such a k exists, and after the loop i == lists.len(),
        // we know that k < i, so by the loop invariant, lists[k].len() <= maxList.len()
        // Therefore l.len() <= maxList.len()
        assert(i == lists.len());
        
        // The proof follows from the loop invariant and the definition of contains
    };
    
    maxList
}

}