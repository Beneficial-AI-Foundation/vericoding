pub fn min_length_sublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires(s.len() > 0)
    ensures(s.contains(minSublist))
    ensures(forall|sublist: Seq<int>| s.contains(sublist) ==> minSublist.len() <= sublist.len())
{
}