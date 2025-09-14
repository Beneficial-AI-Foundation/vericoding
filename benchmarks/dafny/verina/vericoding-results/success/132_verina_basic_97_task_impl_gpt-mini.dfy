// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReplaceAt(a: seq<int>, j: nat, v: int): seq<int>
  requires j < |a|
  { a[..j] + [v] + a[j+1..] }

lemma ReplaceAtSpecs(a: seq<int>, j: nat, v: int)
  requires j < |a|
  ensures |ReplaceAt(a,j,v)| == |a|
  ensures ReplaceAt(a,j,v)[j] == v
  ensures forall k :: 0 <= k < |a| && k != j ==> ReplaceAt(a,j,v)[k] == a[k]
{
}

// </vc-helpers>

// <vc-spec>
method TestArrayElements(a: seq<int>, j: nat) returns (result: seq<int>)
    requires j < |a|
    ensures |result| == |a|
    ensures result[j] == 60
    ensures forall k :: 0 <= k < |a| && k != j ==> result[k] == a[k]
// </vc-spec>
// <vc-code>
{
  result := ReplaceAt(a, j, 60);
}

// </vc-code>
