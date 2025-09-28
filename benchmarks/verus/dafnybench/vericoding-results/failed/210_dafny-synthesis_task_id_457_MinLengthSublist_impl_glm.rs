use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// <vc-code>
{
    let mut min_sublist = s[0];
    let mut i = 1;
    while i < s.len()
        invariant 
            1 <= i <= s.len(),
            exists |k| 0 <= k < i && s[k] == min_sublist,
            forall |j| 0 <= j < i ==> min_sublist.len() <= s[j].len()
    {
        if s[i].len() < min_sublist.len() {
            min_sublist = s[i];
        }
        i = i + 1;
    }
    min_sublist
}
// </vc-code>

fn main() {
}

}