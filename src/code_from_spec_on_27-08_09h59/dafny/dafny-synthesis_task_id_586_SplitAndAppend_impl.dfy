// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  r := l[n..] + l[..n];
}
// </vc-code>
