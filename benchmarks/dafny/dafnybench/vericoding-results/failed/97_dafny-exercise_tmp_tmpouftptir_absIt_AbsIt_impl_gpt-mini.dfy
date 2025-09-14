

// <vc-helpers>
ghost function SeqOf(a: array<int>): seq<int> 
  reads a
{
  a[..]
}

lemma SeqOfLength(a: array<int>) 
  ensures |SeqOf(a)| == a.Length
  reads a
{
  // trivial by definition of SeqOf
}

lemma SeqOfIndex(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures SeqOf(a)[i] == a[i]
  reads a
{
  // follows from definition
}
// </vc-helpers>

// <vc-spec>
method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
// </vc-spec>
// <vc-code>
{
  ghost var orig := SeqOf(s);
  ghost var origLen := |orig|;
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> if orig[j] < 0 then s[j] == -orig[j] else s[j] == orig[j]
    invariant forall k :: i <= k < s.Length ==> s[k] == orig[k]
    invariant s.Length == origLen
    decreases origLen - i
  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
}
// </vc-code>

