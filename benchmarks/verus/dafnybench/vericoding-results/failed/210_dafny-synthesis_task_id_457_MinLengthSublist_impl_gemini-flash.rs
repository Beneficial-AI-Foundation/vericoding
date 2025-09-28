use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_min_length_sublist(s: Seq<Seq<int>>, candidate: Seq<int>) -> bool
    ensures
        is_min_length_sublist(s, candidate) <==>
            s.contains(candidate) && (forall |sublist: Seq<int>| #[trigger] s.contains(sublist) ==> candidate.len() <= sublist.len()),
{
    s.contains(candidate) && (forall |sublist: Seq<int>| #[trigger] s.contains(sublist) ==> candidate.len() <= sublist.len())
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
    let mut min_sublist: Seq<int>;
    let mut i: nat;

    min_sublist = s.index(0);
    i = 1;

    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.contains(min_sublist),
            (forall |k: nat| #[trigger] (k < i) && s.contains(s.index(k)) ==> min_sublist.len() <= s.index(k).len()),
    {
        if s.index(i).len() < min_sublist.len() {
            min_sublist = s.index(i);
        }
        i = i + 1;
    }
    min_sublist
}
// </vc-code>

fn main() {
}

}