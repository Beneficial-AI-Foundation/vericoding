//IMPL RemoveDuplicates
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
  requires a != null
  ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
  result := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in result <==> exists k :: 0 <= k < i && a[k] == x
    invariant forall m, n :: 0 <= m < n < |result| ==> result[m] != result[n]
  {
    if a[i] !in result {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}