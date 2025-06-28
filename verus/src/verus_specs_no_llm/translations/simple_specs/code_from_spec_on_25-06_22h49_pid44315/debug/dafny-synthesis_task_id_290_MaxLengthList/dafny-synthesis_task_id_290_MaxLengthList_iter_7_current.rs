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
    
    // After the loop, we need to prove the postcondition
    assert(forall|l: Seq<int>| lists.contains(l) ==> l.len() <= maxList.len()) by {
        assert forall|l: Seq<int>| lists.contains(l) implies l.len() <= maxList.len() by {
            if lists.contains(l) {
                // Since lists.contains(l), there exists some index k where lists[k] == l
                let k = choose|k: int| 0 <= k < lists.len() && lists[k] == l;
                
                // We know from the loop invariant that after the loop terminates:
                // i == lists.len(), so k < i, which means lists[k].len() <= maxList.len()
                assert(0 <= k < lists.len());
                assert(lists[k] == l);
                assert(k < i); // since i == lists.len()
                assert(lists[k].len() <= maxList.len()); // from loop invariant
                assert(l.len() <= maxList.len()); // since lists[k] == l
            }
        };
    };
    
    maxList
}

}