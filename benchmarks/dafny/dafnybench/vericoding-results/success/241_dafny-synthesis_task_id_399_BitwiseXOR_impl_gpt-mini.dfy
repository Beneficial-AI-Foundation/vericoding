

// <vc-helpers>
// (No helpers required)
// </vc-helpers>

// <vc-spec>
method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var i := 0;
  result := [];
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] ^ b[j]
  {
    result := result + [a[i] ^ b[i]];
    i := i + 1;
  }
}
// </vc-code>

