

// <vc-helpers>
lemma SequenceAppendIndex<T>(s: seq<T>, t: seq<T>, i: int)
  requires 0 <= i < |s| + |t|
  ensures (s + t)[i] == if i < |s| then s[i] else t[i - |s|]
{
}

lemma SequenceLengthAppend<T>(s: seq<T>, t: seq<T>)
  ensures |s + t| == |s| + |t|
{
}

lemma SequenceElementAppend<T>(s: seq<T>, t: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures (s + t)[i] == s[i]
{
}

lemma SequenceElementLast<T>(s: seq<T>, t: seq<T>)
  requires |t| == 1
  ensures (s + t)[|s|] == t[0]
{
}
// </vc-helpers>

// <vc-spec>
method AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var index := 0;
  while index < |a|
    invariant 0 <= index <= |a|
    invariant |result| == index
    invariant forall j :: 0 <= j < index ==> result[j] == a[j] + b[j]
  {
    result := result + [a[index] + b[index]];
    index := index + 1;
  }
}
// </vc-code>

