// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Use seq to check if element already exists, and while loop for copying to fix bound issue. Invariant ensures direct postcondition. */
var result: seq<int> := [];
var i := 0;
while i < arr.Length
  invariant 0 <= i <= arr.Length
  invariant |result| <= i
  invariant forall x, y :: 0 <= x < y < |result| ==> result[x] != result[y]
  invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < |result| && result[j] == arr[k]
{
  var inresult := false;
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant !inresult ==> forall l :: 0 <= l < j ==> result[l] != arr[i]
  {
    if result[j] == arr[i] {
      inresult := true;
    }
    j := j + 1;
  }
  if !inresult {
    result := result + [arr[i]];
  }
  i := i + 1;
}
ret := new int[|result|];
var k := 0;
while k < |result|
  invariant k <= |result|
  invariant forall j :: 0 <= j < k ==> ret[j] == result[j]
{
  ret[k] := result[k];
  k := k + 1;
}
}
// </vc-code>
