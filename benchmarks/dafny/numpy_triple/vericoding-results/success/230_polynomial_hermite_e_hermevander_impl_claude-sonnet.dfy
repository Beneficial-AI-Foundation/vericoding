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
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == deg + 1
    invariant forall k, j :: 0 <= k < i && 0 <= j < |result[k]| ==> result[k][j] == HermiteE(j, x[k])
  {
    var row := [];
    var j := 0;
    while j <= deg
      invariant 0 <= j <= deg + 1
      invariant |row| == j
      invariant forall m :: 0 <= m < j ==> row[m] == HermiteE(m, x[i])
    {
      if j == 0 {
        row := row + [1.0];
      } else if j == 1 {
        row := row + [x[i]];
      } else {
        var val := x[i] * row[j-1] - (j-1) as real * row[j-2];
        row := row + [val];
      }
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
