// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqRemoveAt<T>(s: seq<T>, pos: int): seq<T>
  requires 0 <= pos < |s|
{
  s[..pos] + s[(pos+1)..]
}

lemma SeqRemoveAtProps<T>(s: seq<T>, pos: int)
  requires 0 <= pos < |s|
  ensures |SeqRemoveAt(s, pos)| == |s| - 1
  ensures forall i :: 0 <= i < pos ==> SeqRemoveAt(s, pos)[i] == s[i]
  ensures forall i :: pos <= i < |SeqRemoveAt(s, pos)| ==> SeqRemoveAt(s, pos)[i] == s[i + 1]
{
}

// </vc-helpers>

// <vc-spec>
method RemoveElement(a: array<int>, pos: int) returns (result: seq<int>)
    requires 0 <= pos < a.Length
    ensures |result| == a.Length - 1
    ensures forall i :: 0 <= i < pos ==> result[i] == a[i]
    ensures forall i :: pos <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  var s := a[..];
  assert |s| == a.Length;
  result := SeqRemoveAt(s, pos);
  SeqRemoveAtProps(s, pos);
  assert forall i :: 0 <= i < |s| ==> s[i] == a[i];
}
// </vc-code>
