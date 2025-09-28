use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_contains_implies_exists_index(s: Seq<Seq<int>>, sublist: Seq<int>)
    requires s.contains(sublist)
    ensures exists |k: nat| 0 <= k < s.len() && s[k] == sublist
{
    let k = s.index_of(sublist);
    assert(0 <= k < s.len() && s[k] == sublist);
}
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
    let mut i: nat = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.contains(min_sublist),
            forall |j: nat| 0 <= j < i ==> min_sublist.len() <= s[j].len(),
    {
        if s[i].len() < min_sublist.len() {
            min_sublist = s[i];
        }
        i = i + 1;
    }
    
    proof {
        assert(forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len()) by {
            assert(forall |j: nat| 0 <= j < s.len() ==> min_sublist.len() <= s[j].len());
            assert(forall |sublist: Seq<int>| s.contains(sublist) ==> {
                lemma_contains_implies_exists_index(s, sublist);
                exists |k: nat| 0 <= k < s.len() && s[k] == sublist
            });
        }
    }
    
    min_sublist
}
// </vc-code>

fn main() {
}

}