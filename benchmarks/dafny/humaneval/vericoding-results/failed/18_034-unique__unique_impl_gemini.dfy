// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min_of_set(S: set<int>): int
  requires S != {}
{
  var x :| x in S && forall y :: y in S ==> x <= y;
  x
}

/* helper modified by LLM (iteration 5): changed res.set to set(res) to fix compilation error */
function sorted_sequence_from_set(S: set<int>): (res: seq<int>)
  ensures set(res) == S
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] < res[j]
  decreases S
{
  if S == {} then []
  else
    var m := min_of_set(S);
    [m] + sorted_sequence_from_set(S - {m})
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): changed s.set to set(s) to fix compilation error */
  var s_set := set(s);
  result := sorted_sequence_from_set(s_set);
}
// </vc-code>
