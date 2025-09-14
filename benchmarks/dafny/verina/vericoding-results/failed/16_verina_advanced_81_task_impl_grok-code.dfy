// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added predicate for unique sequences to ensure no duplicates in the result */
predicate IsSorted(s: seq<int>) {
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

function InsertUniqueSorted(s: seq<int>, x: int): (result: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(result)
  ensures x in result[..]
  ensures forall y :: y in s ==> y in result[..]
  ensures forall y :: y in result ==> y == x || y in s[..]
  ensures |result| == |s| || |result| == |s| + 1
  ensures AllUnique(result)
  decreases |s|
{
  if |s| == 0 then [x] else if s[0] < x then [s[0]] + InsertUniqueSorted(s[1..], x) else if s[0] == x then s else [x] + s
}

predicate AllUnique(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate IsUniqueSorted(s: seq<int>) {
  IsSorted(s) && AllUnique(s)
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): refined invariants to include uniqueness of uniqueSeq for better verification */
  var uniqueSeq: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= |uniqueSeq| <= i
    invariant IsUniqueSorted(uniqueSeq)
    invariant forall x :: x in uniqueSeq[..] <==> exists k :: 0 <= k < i && arr[k] == x
  {
    uniqueSeq := InsertUniqueSorted(uniqueSeq, arr[i]);
    i := i + 1;
  }
  result := new int[|uniqueSeq|](i requires 0 <= i < |uniqueSeq| => uniqueSeq[i]);
}
// </vc-code>
