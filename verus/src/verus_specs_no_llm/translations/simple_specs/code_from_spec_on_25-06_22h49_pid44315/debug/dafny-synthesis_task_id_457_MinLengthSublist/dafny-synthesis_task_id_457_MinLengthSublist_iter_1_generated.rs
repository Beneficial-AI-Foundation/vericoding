use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinLengthSublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires
        s.len() > 0
    ensures
        minSublist in s,
        forall |sublist| sublist in s ==> minSublist.len() <= sublist.len()
{
    let mut min_sublist = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            min_sublist in s,
            forall |j| 0 <= j < i ==> min_sublist.len() <= s[j].len()
    {
        if s[i].len() < min_sublist.len() {
            min_sublist = s[i];
        }
        i = i + 1;
    }
    
    min_sublist
}

}