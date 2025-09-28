// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed reverseSeq to use correct Dafny syntax via recursion */
function reverseSeq(m: seq<real>): seq<real>
  decreases |m|
{
  if |m| == 0 then [] else reverseSeq(m[..|m|-1]) + [m[|m|-1]]
}

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement reverse iteratively and prove via invariants */
  var i := |m|;
  result := [];
  while i > 0
    invariant 0 <= i <= |m|
    invariant |result| == |m| - i
    invariant forall k :: 0 <= k < |result| ==> result[k] == m[|m| - 1 - k]
    decreases i
  {
    i := i - 1;
    result := result + [m[i]];
  }
}

// </vc-code>
