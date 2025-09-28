// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): changed seq constructor to an iterative while loop */
  var i := 0;
  result := [];
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == m[|m| - 1 - j]
  {
    result := result + [m[|m| - 1 - i]];
    i := i + 1;
  }
}
// </vc-code>
