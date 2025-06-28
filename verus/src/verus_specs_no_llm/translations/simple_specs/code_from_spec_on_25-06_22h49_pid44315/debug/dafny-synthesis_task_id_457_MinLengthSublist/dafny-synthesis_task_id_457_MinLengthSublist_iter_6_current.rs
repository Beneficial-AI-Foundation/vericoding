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
    
    // Proof that minSublist satisfies the postcondition
    assert forall |sublist: Seq<int>| s.contains(sublist) implies minSublist.len() <= sublist.len() by {
        if s.contains(sublist) {
            // Since s.contains(sublist), there exists an index where sublist appears
            let k = choose |k: int| 0 <= k < s.len() && s[k] == sublist;
            // From our loop invariant and the fact that we processed all elements,
            // we know minSublist.len() <= s[k].len()
            assert(0 <= k < s.len());
            assert(s[k] == sublist);
            if k < i {
                // This case is covered by our loop invariant
                assert(minSublist.len() <= s[k].len());
            }
            // Since s[k] == sublist, we have minSublist.len() <= sublist.len()
            assert(minSublist.len() <= sublist.len());
        }
    };
    
    minSublist
}

}