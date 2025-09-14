

// <vc-helpers>
// No additional helpers required
// </vc-helpers>

// <vc-spec>
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  if |l| == 0 {
    r := l;
  } else {
    r := seq(|l|, i => l[(i - n + |l|) % |l|]);
  }
}
// </vc-code>

