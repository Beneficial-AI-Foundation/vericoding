// SPEC
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
  requires a != null
  ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
}
