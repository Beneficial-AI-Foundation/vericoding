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
        let l = choose|l: Seq<int>| lists.contains(l);
        // Since lists.contains(l), there exists an index k such that lists[k] == l
        let k = choose|k: int| 0 <= k < lists.len() && lists[k] == l;
        // After the loop, i == lists.len(), so our invariant tells us
        // that for all j where 0 <= j < lists.len(), lists[j].len() <= maxList.len()
        // Since k is in this range and lists[k] == l, we have l.len() <= maxList.len()
        assert(lists[k] == l);
        assert(0 <= k < lists.len());
        assert(k < i); // since i == lists.len() after the loop
        assert(lists[k].len() <= maxList.len()); // from the invariant
        assert(l.len() <= maxList.len()); // since lists[k] == l
    };
    
    maxList
}

}