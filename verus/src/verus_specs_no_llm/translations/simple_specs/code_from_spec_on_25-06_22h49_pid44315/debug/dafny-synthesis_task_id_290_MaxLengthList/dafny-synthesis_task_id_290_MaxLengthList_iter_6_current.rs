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
            forall|j: int| 0 <= j < i ==> lists[j].len() <= maxList.len(),
            forall|j: int| 0 <= j < i ==> lists[j].len() <= maxList.len()
    {
        if lists[i as int].len() > maxList.len() {
            maxList = lists[i as int];
        }
        i = i + 1;
    }
    
    // After the loop, i == lists.len()
    assert(i == lists.len());
    
    // Prove that maxList satisfies the postcondition
    assert(forall|l: Seq<int>| lists.contains(l) ==> l.len() <= maxList.len()) by {
        assert forall|l: Seq<int>| lists.contains(l) implies l.len() <= maxList.len() by {
            if lists.contains(l) {
                // There exists an index where l appears in lists
                assert(exists|k: int| 0 <= k < lists.len() && lists[k] == l);
                
                // We can reason about any such index
                assert forall|k: int| (0 <= k < lists.len() && lists[k] == l) implies l.len() <= maxList.len() by {
                    if 0 <= k < lists.len() && lists[k] == l {
                        // Since i == lists.len() after the loop, we have k < i
                        assert(k < i);
                        // From the loop invariant
                        assert(lists[k].len() <= maxList.len());
                        // Since lists[k] == l
                        assert(l.len() <= maxList.len());
                    }
                };
            }
        };
    };
    
    maxList
}

}