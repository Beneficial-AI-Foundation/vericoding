pub fn max_length_list(lists: Seq<Seq<int>>) -> (maxList: Seq<int>)
    requires(lists.len() > 0)
    ensures(forall|l: Seq<int>| lists.contains(l) ==> l.len() <= maxList.len())
    ensures(lists.contains(maxList))
{
}