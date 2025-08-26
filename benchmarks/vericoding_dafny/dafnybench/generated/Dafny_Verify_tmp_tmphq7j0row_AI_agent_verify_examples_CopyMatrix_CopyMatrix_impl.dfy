method CopyMatrix(src: array2<int>, dst: array2<int>)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
</vc-spec>
<vc-code>
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall i', j :: 0 <= i' < i && 0 <= j < src.Length1 ==> dst[i',j] == old(src[i',j])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall i', j' :: 0 <= i' < i && 0 <= j' < src.Length1 ==> dst[i',j'] == old(src[i',j'])
      invariant forall j' :: 0 <= j' < j ==> dst[i,j'] == old(src[i,j'])
      invariant forall i', j' :: 0 <= i' < src.Length0 && 0 <= j' < src.Length1 ==> src[i',j'] == old(src[i',j'])
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}
</vc-code>
<vc-helpers>
</vc-helpers>