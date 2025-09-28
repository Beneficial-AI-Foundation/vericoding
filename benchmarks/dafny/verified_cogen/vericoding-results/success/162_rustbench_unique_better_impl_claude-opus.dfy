// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsUnique(s: seq<int>, i: int)
  requires 0 <= i < |s|
{
  forall j :: 0 <= j < i ==> s[j] != s[i]
}

function RemoveDuplicates(a: array<int>, n: int): seq<int>
  requires 0 <= n <= a.Length
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  reads a
  ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(a, n)| ==> RemoveDuplicates(a, n)[i] < RemoveDuplicates(a, n)[j]
  decreases n
{
  if n == 0 then []
  else
    var prev := RemoveDuplicates(a, n-1);
    if |prev| == 0 || prev[|prev|-1] < a[n-1] then
      prev + [a[n-1]]
    else
      prev
}
// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  result := [];
  if a.Length == 0 {
    return;
  }
  
  result := [a[0]];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant |result| >= 1
    invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
    invariant result[|result|-1] <= a[i-1]
    invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] >= a[j]
  {
    if a[i] > result[|result|-1] {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
