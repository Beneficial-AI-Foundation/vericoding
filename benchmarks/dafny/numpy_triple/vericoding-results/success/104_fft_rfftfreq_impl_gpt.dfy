// <vc-preamble>
// Type alias to represent finite precision floating point numbers
type Float = real
// </vc-preamble>

// <vc-helpers>
function freqVal(i: nat, n: nat, d: Float): Float
  requires n > 0
  requires d > 0.0
{
  (i as Float) / (d * (n as Float))
}

lemma DivPresLe(a: real, b: real, c: real)
  requires a <= b
  requires c > 0.0
  ensures a / c <= b / c
{
}

lemma MonotoneFreqIndices(n: nat, d: Float, i: nat, j: nat)
  requires n > 0 && d > 0.0 && i <= j
  ensures freqVal(i, n, d) <= freqVal(j, n, d)
{
  var denom := d * (n as Float);
  assert denom > 0.0;
  assert (i as Float) <= (j as Float);
  DivPresLe(i as Float, j as Float, denom);
}

lemma MonotoneFreqAll(n: nat, d: Float)
  requires n > 0 && d > 0.0
  ensures forall i, j :: 0 <= i <= j <= n / 2 ==> freqVal(i, n, d) <= freqVal(j, n, d)
{
  forall i, j | 0 <= i <= j <= n / 2
    ensures freqVal(i, n, d) <= freqVal(j, n, d)
  {
    MonotoneFreqIndices(n, d, i, j);
  }
}
// </vc-helpers>

// <vc-spec>
method numpy_rfftfreq(n: nat, d: Float) returns (result: seq<Float>)
  // Preconditions: positive window length and sample spacing
  requires n > 0
  requires d > 0.0
  
  // Postconditions specify the exact behavior of rfftfreq
  ensures |result| == n / 2 + 1
  
  // First element is always 0
  ensures result[0] == 0.0
  
  // Each element follows the frequency formula: f[i] = i / (d * n)
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == (i as Float) / (d * (n as Float))
  
  // Last element is the Nyquist frequency
  ensures result[n / 2] == (n / 2) as Float / (d * (n as Float))
  
  // Frequencies are monotonically non-decreasing
  ensures forall i, j :: 0 <= i <= j < |result| ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
{
  var len: nat := n / 2 + 1;
  var s: seq<Float> := [];
  var i: nat := 0;
  while i < len
    invariant i <= len
    invariant |s| == i
    invariant forall k :: 0 <= k < |s| ==> s[k] == freqVal(k, n, d)
    decreases len - i
  {
    s := s + [freqVal(i, n, d)];
    i := i + 1;
  }
  MonotoneFreqAll(n, d);
  result := s;
}
// </vc-code>
