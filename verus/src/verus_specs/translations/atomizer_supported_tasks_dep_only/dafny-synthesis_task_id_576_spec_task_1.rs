pub fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures(true <== (exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len())))
{
}