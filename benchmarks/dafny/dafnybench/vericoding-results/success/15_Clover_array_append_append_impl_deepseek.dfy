

// <vc-helpers>
lemma ArrayExtensionality(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  requires forall i :: 0 <= i < a.Length ==> a[i] == b[i]
  ensures a[..] == b[..]
{
}

lemma SequenceExtensionality<s>(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
  ensures a == b
{
}
// </vc-helpers>

// <vc-spec>
method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// <vc-code>
{
  var len := a.Length;
  c := new int[len + 1];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
  {
    c[i] := a[i];
    i := i + 1;
  }
  c[len] := b;
}
// </vc-code>

