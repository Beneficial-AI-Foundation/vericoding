// <vc-preamble>
// Complex number datatype for FFT operations
datatype Complex = Complex(re: real, im: real)

// Helper predicate to check if a sequence is Hermitian-symmetric
predicate isHermitianSymmetric(a: seq<Complex>)
{
    |a| > 0 && 
    forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i + j == |a| - 1 ==>
        a[i].re == a[j].re && a[i].im == -a[j].im
}

// Main irfft method - computes inverse real-valued FFT
// </vc-preamble>

// <vc-helpers>
function cos(angle: real): real
  decreases if angle < 0.0 then -angle else angle
{
  /* helper modified by LLM (iteration 5): Added decreases clause and fixed termination */
  if angle < 0.0 then cos(-angle)
  else if angle > 2.0 * 3.141592653589793 then cos(angle - 2.0 * 3.141592653589793)
  else if angle > 3.141592653589793 then -cos(angle - 3.141592653589793)
  else if angle > 1.5707963267948966 then -sin(3.141592653589793 - angle)
  else if angle > 0.7853981633974483 then sin(1.5707963267948966 - angle)
  else 1.0 - angle * angle / 2.0
}

function sin(angle: real): real
  decreases if angle < 0.0 then -angle else angle
{
  /* helper modified by LLM (iteration 5): Added decreases clause and fixed termination */
  if angle < 0.0 then -sin(-angle)
  else if angle > 2.0 * 3.141592653589793 then sin(angle - 2.0 * 3.141592653589793)
  else if angle > 3.141592653589793 then -sin(angle - 3.141592653589793)
  else if angle > 1.5707963267948966 then sin(3.141592653589793 - angle)
  else if angle > 0.7853981633974483 then cos(1.5707963267948966 - angle)
  else angle - angle * angle * angle / 6.0
}

function computeTwiddleFactor(k: int, N: int): Complex
  requires N > 0
{
  var angle := -2.0 * 3.141592653589793 * k as real / (2.0 * N as real);
  Complex(cos(angle), sin(angle))
}

function scaleReal(c: Complex, factor: real): Complex
{
  Complex(c.re * factor, c.im * factor)
}

function complexAdd(a: Complex, b: Complex): Complex
{
  Complex(a.re + b.re, a.im + b.im)
}

function conjugate(c: Complex): Complex
{
  Complex(c.re, -c.im)
}

lemma hermitianConjugateLemma(a: seq<Complex>, i: int)
  requires isHermitianSymmetric(a)
  requires 0 <= i < |a|
  ensures a[|a| - 1 - i] == conjugate(a[i])
{
}

function complexMultiply(a: Complex, b: Complex): Complex
{
  Complex(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
}

function complexSubtract(a: Complex, b: Complex): Complex
{
  Complex(a.re - b.re, a.im - b.im)
}
// </vc-helpers>

// <vc-spec>
method irfft(a: seq<Complex>, n: nat) returns (result: seq<real>)
    // Input must be non-empty and Hermitian-symmetric
    requires |a| > 0
    requires isHermitianSymmetric(a)
    // Length relationship: output length is twice input length minus 2
    requires n == 2 * (|a| - 1)
    
    // Output length matches specified n
    ensures |result| == n
    // DC component preservation: if input DC component is real, it appears in output
    ensures a[0].im == 0.0 ==> exists i :: 0 <= i < |result| && result[i] == a[0].re
    // Length relationship is preserved
    ensures n == 2 * (|a| - 1)
    // Input constraint is maintained
    ensures isHermitianSymmetric(a)
    // Real-valued output symmetry: result exhibits properties of real-valued inverse FFT
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| && i + j == |result| ==> 
        result[i] == result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed array bounds and index calculations */
  var N := |a|;
  var complexOutput : seq<Complex> := [];
  var twiddleFactors : seq<Complex> := [];
  var invN := 1.0 / n as real;
  
  // Initialize complexOutput sequence with zeros
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |complexOutput| == idx
  {
    complexOutput := complexOutput + [Complex(0.0, 0.0)];
    idx := idx + 1;
  }
  
  // Precompute twiddle factors - only need N factors, not n
  var k := 0;
  while k < N
    invariant 0 <= k <= N
    invariant |twiddleFactors| == k
  {
    twiddleFactors := twiddleFactors + [computeTwiddleFactor(k, n)];
    k := k + 1;
  }
  
  // Convert Hermitian-symmetric input to real output
  k := 0;
  while k < N
    invariant 0 <= k <= N
  {
    if k == 0 || k == N - 1 {
      // DC and Nyquist components are real
      complexOutput := complexOutput[k := Complex(a[k].re * 2.0 * invN, a[k].im * 2.0 * invN)];
    } else {
      var conj := conjugate(a[N - 1 - k]);
      var evenPart := complexAdd(a[k], conj);
      var oddPart := complexMultiply(twiddleFactors[k], complexSubtract(a[k], conj));
      complexOutput := complexOutput[k := Complex(evenPart.re * invN, evenPart.im * invN)];
      if n - k < n {
        complexOutput := complexOutput[n - k := Complex(oddPart.re * invN, oddPart.im * invN)];
      }
    }
    k := k + 1;
  }
  
  // Convert complex output to real by taking real parts
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
  {
    result := result + [complexOutput[i].re];
    i := i + 1;
  }
}
// </vc-code>
