method Merge(a: array<int>, b: array<int>) returns (output: array<int>)
  requires sorted(a[..])
  requires sorted(b[..])
  ensures sorted(output[..])
  ensures multiset(output[..]) == multiset(a[..]) + multiset(b[..])
{
  output := new int[a.Length + b.Length];
  var i, j, k := 0, 0, 0;
  
  while i < a.Length || j < b.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant k == i + j
    invariant sorted(output[..k])
    invariant i < a.Length ==> k == 0 || output[k-1] <= a[i]
    invariant j < b.Length ==> k == 0 || output[k-1] <= b[j]
    invariant multiset(output[..k]) == multiset(a[..i]) + multiset(b[..j])
  {
    if i >= a.Length {
      output[k] := b[j];
      j := j + 1;
    } else if j >= b.Length {
      output[k] := a[i];
      i := i + 1;
    } else if a[i] <= b[j] {
      output[k] := a[i];
      i := i + 1;
    } else {
      output[k] := b[j];
      j := j + 1;
    }
    k := k + 1;
  }
}

predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}