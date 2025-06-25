pub fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures(result <==> (exists|i: int| 0 <= i < list.len() && sub == list[i]))
{
}