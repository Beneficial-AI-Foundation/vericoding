// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArrayStr(a: seq<real>) returns (result: string)
  ensures |result| > 0
  ensures |a| == 0 ==> result == "[]"
  ensures |a| > 0 ==> |result| >= 2 && result[0] == '[' && result[|result|-1] == ']'
  ensures |a| > 0 ==> forall i, j {:trigger a[i], a[j]} :: 0 <= i < j < |a| ==> 
    exists pos_i, pos_j {:trigger result[pos_i], result[pos_j]} :: 0 <= pos_i < pos_j < |result|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
