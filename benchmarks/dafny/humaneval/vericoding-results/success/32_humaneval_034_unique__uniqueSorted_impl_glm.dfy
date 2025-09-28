// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: seq<int>, x: int): bool {
  exists i :: 0 <= i < |s| && s[i] == x
}

predicate IsUnique(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function RemoveDuplicates(s: seq<int>): seq<int> {
  if |s| == 0 then []
  else if Contains(s[1..], s[0]) then RemoveDuplicates(s[1..])
  else [s[0]] + RemoveDuplicates(s[1..])
}
/* helper modified by LLM (iteration 2): added helper functions for contains, uniqueness, and duplicate removal */
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
  /* code modified by LLM (iteration 2): fixed postcondition by ensuring strict ordering */
  var processed: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] in processed
    invariant IsUnique(processed)
    invariant forall j :: 0 <= j < |processed| ==> processed[j] in s
    invariant forall j :: 0 <= j < i ==> s[j] in processed
    invariant forall j :: 0 <= j < |processed| ==> (exists k :: 0 <= k < i && s[k] == processed[j])
    invariant forall k, l :: 0 <= k < l < |processed| ==> processed[k] < processed[l]
  {
    if i == 0 || s[i] != s[i-1] {
      processed := processed + [s[i]];
    }
    i := i + 1;
  }
  result := processed;
}
// </vc-code>
