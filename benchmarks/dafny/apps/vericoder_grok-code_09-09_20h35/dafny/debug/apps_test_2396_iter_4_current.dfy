predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(result: seq<int>, input: string)
{
    |result| >= 0 &&
    (forall i :: 0 <= i < |result| ==> result[i] >= 1) &&
    (forall i :: 0 <= i < |result| ==> result[i] <= |result|)
}

// <vc-helpers>
function BuildSeq(n: int): seq<int>
  requires n >= 0
  ensures |result| == n
  ensures (forall i :: 0 <= i < n ==> result[i] == i+1)
{
  if n == 0 then [] else BuildSeq(n-1) + [n]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(result, input)
// </vc-spec>
// <vc-code>
{ 
  var n := |input|; 
  var r := BuildSeq(n); 
  result := r; 
}
// </vc-code>

