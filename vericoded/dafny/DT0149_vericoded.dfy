// <vc-preamble>
// Method to compute discrete Fourier Transform sample frequencies
// Returns frequencies arranged in standard DFT order: positive frequencies first, then negative
// </vc-preamble>

// <vc-helpers>

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
  var N := (n + 1) / 2;
  var frequencies := [];
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant |frequencies| == i
    invariant forall j :: 0 <= j < i ==> frequencies[j] == (j as real) / (d * (n as real))
  {
    frequencies := frequencies + [(i as real) / (d * (n as real))];
    i := i + 1;
  }
  
  i := N;
  while i < n
    invariant N <= i <= n
    invariant |frequencies| == i
    invariant forall j :: 0 <= j < N ==> frequencies[j] == (j as real) / (d * (n as real))
    invariant forall j :: N <= j < i ==> frequencies[j] == ((j as int) - (n as int)) as real / (d * (n as real))
  {
    frequencies := frequencies + [((i as int) - (n as int)) as real / (d * (n as real))];
    i := i + 1;
  }
  
  result := frequencies;
}
// </vc-code>
