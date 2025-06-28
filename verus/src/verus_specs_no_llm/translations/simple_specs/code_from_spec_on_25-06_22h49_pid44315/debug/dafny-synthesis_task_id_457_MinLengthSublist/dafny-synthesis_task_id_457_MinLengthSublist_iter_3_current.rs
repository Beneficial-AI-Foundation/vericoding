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
    assert(forall |sublist: Seq<int>| s.contains(sublist) ==> minSublist.len() <= sublist.len()) by {
        assert forall |sublist: Seq<int>| s.contains(sublist) implies minSublist.len() <= sublist.len() by {
            if s.contains(sublist) {
                // sublist must be at some index in s
                assert(exists |k: int| 0 <= k < s.len() && s[k] == sublist);
                let idx = choose |k: int| 0 <= k < s.len() && s[k] == sublist;
                // From the loop invariant, we know minSublist.len() <= s[idx].len()
                assert(minSublist.len() <= s[idx].len());
                assert(s[idx] == sublist);
            }
        }
    };
    
    minSublist
}

}