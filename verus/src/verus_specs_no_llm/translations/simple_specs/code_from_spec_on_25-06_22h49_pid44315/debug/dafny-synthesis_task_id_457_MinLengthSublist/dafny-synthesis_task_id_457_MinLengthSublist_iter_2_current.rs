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
    let mut min_sublist = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.contains(min_sublist),
            forall |j| 0 <= j < i ==> min_sublist.len() <= s[j].len()
    {
        if s[i].len() < min_sublist.len() {
            min_sublist = s[i];
        }
        i = i + 1;
    }
    
    // Proof that min_sublist satisfies the postcondition
    assert(forall |sublist| s.contains(sublist) ==> minSublist.len() <= sublist.len()) by {
        assert forall |sublist| s.contains(sublist) implies minSublist.len() <= sublist.len() by {
            if s.contains(sublist) {
                // sublist must be at some index in s
                let idx = choose |k| 0 <= k < s.len() && s[k] == sublist;
                // From the loop invariant, we know min_sublist.len() <= s[idx].len()
                assert(minSublist.len() <= s[idx].len());
                assert(s[idx] == sublist);
            }
        }
    };
    
    min_sublist
}

}