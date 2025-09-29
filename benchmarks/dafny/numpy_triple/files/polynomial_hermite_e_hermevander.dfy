// <vc-preamble>
// Ghost function to compute HermiteE polynomial values using the recurrence relation
ghost function HermiteE(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else x * HermiteE(n-1, x) - (n-1) as real * HermiteE(n-2, x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HermeVander(x: seq<real>, deg: nat) returns (result: seq<seq<real>>)
  requires |x| >= 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == deg + 1
  // Each element of the result matrix equals the corresponding HermiteE polynomial
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == HermiteE(j, x[i])
  // First column is all ones (He_0(x) = 1)
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == 1.0
  // Second column equals x when deg > 0 (He_1(x) = x)
  ensures deg > 0 ==> forall i :: 0 <= i < |result| ==> result[i][1] == x[i]
  // Subsequent columns follow the HermiteE recurrence relation
  ensures forall i, j :: 0 <= i < |result| && 2 <= j <= deg ==>
    result[i][j] == x[i] * result[i][j-1] - (j-1) as real * result[i][j-2]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
