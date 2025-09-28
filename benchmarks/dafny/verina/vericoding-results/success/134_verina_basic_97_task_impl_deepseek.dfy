// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma IndexInRange(s: seq<int>, i: nat)
  requires i < |s|
  ensures 0 <= i < |s|
{
}

function updateSeq<T>(s: seq<T>, index: int, value: T): seq<T>
  requires 0 <= index < |s|
  ensures |updateSeq(s, index, value)| == |s|
  ensures updateSeq(s, index, value)[index] == value
  ensures forall k :: 0 <= k < |s| && k != index ==> updateSeq(s, index, value)[k] == s[k]
{
  s[0..index] + [value] + s[index+1..]
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
  IndexInRange(a, j);
  result := updateSeq(a, j, 60);
}
// </vc-code>
