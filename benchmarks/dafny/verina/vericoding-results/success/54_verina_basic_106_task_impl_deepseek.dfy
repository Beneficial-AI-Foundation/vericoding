// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function add(a: int, b: int): int { a + b }

function zip_sum(a: seq<int>, b: seq<int>, i: int): int
  requires 0 <= i < |a| && |a| == |b|
{
  a[i] + b[i]
}

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
    result := seq(|a|, i requires 0 <= i < |a| => a[i] + b[i]);
}
// </vc-code>
