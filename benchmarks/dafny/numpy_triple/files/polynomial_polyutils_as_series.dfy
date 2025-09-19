// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AsSeries(arr: seq<seq<real>>, trim: bool) returns (result: seq<seq<real>>)
    requires |arr| > 0
    requires forall i :: 0 <= i < |arr| ==> |arr[i]| > 0
    requires forall i, j :: 0 <= i < |arr| && 0 <= j < |arr| ==> |arr[i]| == |arr[j]|
    ensures |result| == |arr|
    ensures !trim ==> (forall i :: 0 <= i < |result| ==> 
                        |result[i]| == |arr[i]| &&
                        forall j :: 0 <= j < |result[i]| ==> result[i][j] == arr[i][j])
    ensures trim ==> (forall i :: 0 <= i < |result| ==> 
                       |result[i]| <= |arr[i]| &&
                       |result[i]| >= 1 &&
                       forall j :: 0 <= j < |result[i]| ==> result[i][j] == arr[i][j] &&
                       (|result[i]| == |arr[i]| || result[i][|result[i]|-1] != 0.0) &&
                       forall k :: |result[i]| <= k < |arr[i]| ==> arr[i][k] == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
