

// <vc-helpers>
function drop(n: int, l: seq<int>): seq<int>
  requires 0 <= n <= |l|
{
  l[n..]
}

function take(n: int, l: seq<int>): seq<int>
  requires 0 <= n <= |l|
{
  l[..n]
}
// </vc-helpers>

// <vc-spec>
method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
// </vc-spec>
// <vc-code>
{
  return drop(n, l) + take(n, l);
}
// </vc-code>

