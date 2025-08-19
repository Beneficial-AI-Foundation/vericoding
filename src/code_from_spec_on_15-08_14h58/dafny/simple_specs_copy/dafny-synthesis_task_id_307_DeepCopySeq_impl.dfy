//IMPL
method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
  ensures |copy| == |s|
  ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
  copy := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |copy| == i
    invariant forall j :: 0 <= j < i ==> copy[j] == s[j]
  {
    copy := copy + [s[i]];
    i := i + 1;
  }
}