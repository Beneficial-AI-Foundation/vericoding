pub fn Cubes(n: int) -> (s: Seq<int>)
    requires n >= 0
    ensures |s| == n
    ensures forall|i: int| 0 <= i < n ==> s[i] == i*i*i
{
}

pub fn empty_Lemma(r: Seq<int>)
    ensures r == Seq::empty()
{
}