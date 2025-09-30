// <vc-preamble>
// Ghost function for real number exponentiation with natural number exponents
ghost function Pow(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Pow(base, exp - 1)
}

// Generate a Vandermonde matrix with decreasing powers (default behavior)
// The Vandermonde matrix is a matrix with terms of a geometric progression in each row
// For input vector x of length n and m columns, entry (i,j) = x[i]^(m-1-j)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove RealPow equals Pow */
function RealPow(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * RealPow(base, exp - 1)
}

lemma RealPowEqualsPow(base: real, exp: nat)
    ensures RealPow(base, exp) == Pow(base, exp)
    decreases exp
{
    if exp == 0 {
    } else {
        RealPowEqualsPow(base, exp - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method Vander(x: seq<real>, m: nat) returns (result: seq<seq<real>>)
    requires m > 0
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == m
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < m ==> 
            result[i][j] == Pow(x[i], (m - 1 - j) as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Call lemma to verify RealPow equals Pow */
{
  result := [];
  for i := 0 to |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == m
    invariant forall k, j :: 0 <= k < i && 0 <= j < m ==> result[k][j] == Pow(x[k], (m - 1 - j) as nat)
  {
    var row := [];
    for j := 0 to m
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == Pow(x[i], (m - 1 - k) as nat)
    {
      var power := RealPow(x[i], (m - 1 - j) as nat);
      RealPowEqualsPow(x[i], (m - 1 - j) as nat);
      row := row + [power];
    }
    result := result + [row];
  }
}
// </vc-code>
