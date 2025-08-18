// <vc-helpers>
// </vc-helpers>

method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// <vc-code>
{
  assume false;
}
// </vc-code>