// <vc-preamble>
// Method to compute discrete Fourier Transform sample frequencies
// Returns frequencies arranged in standard DFT order: positive frequencies first, then negative
// </vc-preamble>

// <vc-helpers>
function computeBoundary(n: nat): int { (n + 1) / 2 }

function computeFrequency(i: int, n: nat, d: real): real
  requires n > 0
  requires d != 0.0
{
  var N := computeBoundary(n);
  if i < N then
    (i as real) / (d * (n as real))
  else
    (((i as int) - (n as int)) as real) / (d * (n as real))
}
// </vc-helpers>

// <vc-spec>
method fftfreq(n: nat, d: real) returns (result: seq<real>)
  // Preconditions: non-empty array and valid sample spacing
  requires n > 0
  requires d != 0.0
  
  // Postconditions: precise frequency computation according to DFT convention
  ensures |result| == n
  
  // DC component (index 0) is always zero
  ensures result[0] == 0.0
  
  // Define the boundary between positive and negative frequencies
  ensures var N := (n + 1) / 2;
          // For indices in first half: positive frequencies i / (d*n)
          (forall i :: 0 <= i < N ==> 
            result[i] == (i as real) / (d * (n as real))) &&
          // For indices in second half: negative frequencies (i-n) / (d*n)  
          (forall i :: N <= i < n ==> 
            result[i] == ((i as int) - (n as int)) as real / (d * (n as real)))
// </vc-spec>
// <vc-code>
{
  var N := computeBoundary(n);
  result := [];
  var i := 0;
  while i < n
    invariant |result| == i
    invariant i >= 0
    invariant i <= n
    invariant forall j :: 0 <= j < i ==> result[j] == computeFrequency(j, n, d)
  {
    result := result + [computeFrequency(i, n, d)];
    i := i + 1;
  }
}
// </vc-code>
