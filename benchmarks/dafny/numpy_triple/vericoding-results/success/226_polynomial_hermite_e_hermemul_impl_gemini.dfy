// <vc-preamble>
// Multiply two Hermite series represented as coefficient sequences
// The product of Hermite polynomials requires reprojection onto the basis set
// </vc-preamble>

// <vc-helpers>
function min(a: nat, b: nat): nat {
  if a < b then a else b
}

function Power(base: real, exp: nat): real {
  if exp == 0 then 1.0 else base * Power(base, exp - 1)
}

/* helper modified by LLM (iteration 2): added ensures clause to Factorial to help prove non-zero divisor */
function Factorial(n: nat): real
  ensures Factorial(n) > 0.0
{
  if n == 0 then 1.0 else (n as real) * Factorial(n - 1)
}

function HermiteProductCoeff(m: nat, n: nat, k: nat): real
  requires k <= m && k <= n
{
  var denom := Factorial(m - k) * Factorial(n - k) * Factorial(k);
  (Power(2.0, k) * Factorial(m) * Factorial(n)) / denom
}
// </vc-helpers>

// <vc-spec>
method hermemul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0 && |c2| > 0
  ensures |result| == |c1| + |c2| - 1
  // Zero preservation: if either input is all zeros, result is all zeros
  ensures (forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) || 
          (forall j :: 0 <= j < |c2| ==> c2[j] == 0.0) ==> 
          (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed invariant on inner-most loop for zero-input property */
  var n1 := |c1|;
  var n2 := |c2|;
  var out_len := n1 + n2 - 1;
  result := seq(out_len, _ => 0.0);

  var i: nat := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant |result| == out_len
    invariant (forall i' :: 0 <= i' < |c1| ==> c1[i'] == 0.0) || (forall j' :: 0 <= j' < |c2| ==> c2[j'] == 0.0) ==> (forall k' :: 0 <= k' < |result| ==> result[k'] == 0.0)
  {
    var j: nat := 0;
    while j < n2
      invariant 0 <= j <= n2
      invariant |result| == out_len
      invariant 0 <= i < n1
      invariant (forall i' :: 0 <= i' < |c1| ==> c1[i'] == 0.0) || (forall j' :: 0 <= j' < |c2| ==> c2[j'] == 0.0) ==> (forall k' :: 0 <= k' < |result| ==> result[k'] == 0.0)
    {
      var k: nat := 0;
      var m_ij := min(i, j);
      while k <= m_ij
        invariant 0 <= k <= m_ij + 1
        invariant |result| == out_len
        invariant 0 <= i < n1 && 0 <= j < n2
        invariant (forall i' :: 0 <= i' < |c1| ==> c1[i'] == 0.0) || (forall j' :: 0 <= j' < |c2| ==> c2[j'] == 0.0) ==> (forall k' :: 0 <= k' < |result| ==> result[k'] == 0.0)
      {
        var l := i + j - 2*k;
        var coeff := HermiteProductCoeff(i,j,k);
        var product_term := c1[i] * c2[j] * coeff;
        if product_term != 0.0 {
          result := result[l := result[l] + product_term];
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
