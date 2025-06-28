use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinLengthSublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires
        s.len() > 0
    ensures
        s.contains(minSublist),
        forall |sublist| s.contains(sublist) ==> minSublist.len() <= sublist.len()
{
    let mut minSublist = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.contains(minSublist),
            forall |j: int| 0 <= j < i ==> minSublist.len() <= s[j].len()
    {
        if s[i].len() < minSublist.len() {
            minSublist = s[i];
        }
        i = i + 1;
    }
    
    // At this point, i == s.len(), so the invariant gives us what we need
    assert(forall |j: int| 0 <= j < s.len() ==> minSublist.len() <= s[j].len());
    
    // Proof that minSublist satisfies the postcondition
    assert(forall |sublist: Seq<int>| s.contains(sublist) ==> minSublist.len() <= sublist.len()) by {
        assert forall |sublist: Seq<int>| s.contains(sublist) implies minSublist.len() <= sublist.len() by {
            if s.contains(sublist) {
                // Since s.contains(sublist), there exists an index where sublist appears
                assert(exists |k: int| 0 <= k < s.len() && s[k] == sublist);
                let k = choose |k: int| 0 <= k < s.len() && s[k] == sublist;
                // From our assertion above, we know minSublist.len() <= s[k].len()
                assert(minSublist.len() <= s[k].len());
                // Since s[k] == sublist, we have minSublist.len() <= sublist.len()
                assert(minSublist.len() <= sublist.len());
            }
        }
    };
    
    minSublist
}

}