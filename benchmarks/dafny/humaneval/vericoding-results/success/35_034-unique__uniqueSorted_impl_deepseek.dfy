// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed base cases and induction step for strict ordering proof */
function RemoveDuplicates(s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures |RemoveDuplicates(s)| <= |s|
  ensures forall x :: x in RemoveDuplicates(s) ==> x in s
  ensures forall x :: x in s ==> x in RemoveDuplicates(s)
  ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(s)| ==> RemoveDuplicates(s)[i] < RemoveDuplicates(s)[j]
  decreases |s|
{
  if |s| == 0 then []
  else if |s| == 1 then [s[0]]
  else 
    var tail := RemoveDuplicates(s[1..]);
    if |tail| == 0 then [s[0]]
    else if s[0] == tail[0] then tail
    else [s[0]] + tail
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
/* code modified by LLM (iteration 5): Call helper function directly */
{
  result := RemoveDuplicates(s);
}
// </vc-code>
