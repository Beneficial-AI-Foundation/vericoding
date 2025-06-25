pub fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires(n >= 0)
    ensures(|r| == |l|)
    ensures(forall|i: int| 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|])
{
}