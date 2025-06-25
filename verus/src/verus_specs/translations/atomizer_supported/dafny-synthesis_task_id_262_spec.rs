pub fn SplitArray(arr: &[int], L: int) -> (firstPart: Seq<int>, secondPart: Seq<int>)
    requires 0 <= L <= arr.len()
    ensures |firstPart| == L
    ensures |secondPart| == arr.len() - L
    ensures firstPart + secondPart == arr@
{
}