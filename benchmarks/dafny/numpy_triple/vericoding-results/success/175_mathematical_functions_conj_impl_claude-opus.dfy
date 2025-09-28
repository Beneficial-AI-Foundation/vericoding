// <vc-preamble>
// Complex number representation with real and imaginary components
datatype Complex = Complex(re: real, im: real)

// Complex number addition operation
function ComplexAdd(z: Complex, w: Complex): Complex
{
    Complex(z.re + w.re, z.im + w.im)
}

// Complex number multiplication operation  
function ComplexMul(z: Complex, w: Complex): Complex
{
    Complex(z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re)
}

// Magnitude squared of a complex number
function ComplexNormSq(z: Complex): real
{
    z.re * z.re + z.im * z.im
}

// Complex conjugate of a single complex number
function ComplexConj(z: Complex): Complex
{
    Complex(z.re, -z.im)
}

// Main method: compute complex conjugate element-wise for a sequence of complex numbers
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Conj(x: seq<Complex>) returns (result: seq<Complex>)
    ensures |result| == |x|
    // Basic definition: conj(a + bi) = a - bi
    ensures forall i :: 0 <= i < |x| ==> result[i] == Complex(x[i].re, -x[i].im)
    // Real preservation: for purely real numbers, conj(x) = x
    ensures forall i :: 0 <= i < |x| && x[i].im == 0.0 ==> result[i] == x[i]
    // Involution property: conj(conj(x)) = x
    ensures forall i :: 0 <= i < |x| ==> ComplexConj(result[i]) == x[i]
    // Magnitude preservation: |conj(x)| = |x|
    ensures forall i :: 0 <= i < |x| ==> ComplexNormSq(x[i]) == ComplexNormSq(result[i])
    // Distributive over addition: conj(x + y) = conj(x) + conj(y)
    ensures forall i :: 0 <= i < |x| ==> forall y: Complex ::
        ComplexConj(ComplexAdd(x[i], y)) == ComplexAdd(result[i], ComplexConj(y))
    // Distributive over multiplication: conj(x * y) = conj(x) * conj(y)
    ensures forall i :: 0 <= i < |x| ==> forall y: Complex ::
        ComplexConj(ComplexMul(x[i], y)) == ComplexMul(result[i], ComplexConj(y))
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Complex(x[j].re, -x[j].im)
    invariant forall j :: 0 <= j < i && x[j].im == 0.0 ==> result[j] == x[j]
    invariant forall j :: 0 <= j < i ==> ComplexConj(result[j]) == x[j]
    invariant forall j :: 0 <= j < i ==> ComplexNormSq(x[j]) == ComplexNormSq(result[j])
    invariant forall j :: 0 <= j < i ==> forall y: Complex ::
        ComplexConj(ComplexAdd(x[j], y)) == ComplexAdd(result[j], ComplexConj(y))
    invariant forall j :: 0 <= j < i ==> forall y: Complex ::
        ComplexConj(ComplexMul(x[j], y)) == ComplexMul(result[j], ComplexConj(y))
  {
    var conj := ComplexConj(x[i]);
    result := result + [conj];
    i := i + 1;
  }
}
// </vc-code>
