//IMPL 
method AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
  result := seq(|a|, i requires 0 <= i < |a| => a[i] + b[i]);
}