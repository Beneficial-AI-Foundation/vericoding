// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate isUnique(s: seq<int>, i: int)
  requires 0 <= i < |s|
{
  forall j :: 0 <= j < i ==> s[j] != s[i]
}
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)

    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
    invariant forall x :: x in result ==> x in s[..i]
    invariant forall x :: x in s[..i] ==> x in result
    invariant |result| == 0 || (i > 0 && result[|result|-1] <= s[i-1])
  {
    if |result| == 0 || result[|result|-1] < s[i] {
      result := result + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
