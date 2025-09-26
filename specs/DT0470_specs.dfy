// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LaguerreMul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0
  requires |c2| > 0
  ensures |result| == |c1| + |c2| - 1
  ensures forall i :: 0 <= i < |result| ==> 
    (result[i] != 0.0 ==> 
      exists j, k :: 0 <= j < |c1| && 0 <= k < |c2| && 
        j + k == i && c1[j] != 0.0 && c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
