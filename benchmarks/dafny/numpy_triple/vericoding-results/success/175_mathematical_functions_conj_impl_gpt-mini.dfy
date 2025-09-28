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
/* helper modified by LLM (iteration 4): involutive property of conjugation */
lemma Conj_involutive(z: Complex)
  ensures ComplexConj(ComplexConj(z)) == z
{
  assert ComplexConj(z) == Complex(z.re, -z.im);
  assert ComplexConj(ComplexConj(z)) == Complex(ComplexConj(z).re, -ComplexConj(z).im);
  assert ComplexConj(ComplexConj(z)) == Complex(z.re, -(-z.im));
  assert -(-z.im) == z.im;
  assert ComplexConj(ComplexConj(z)) == Complex(z.re, z.im);
  assert Complex(z.re, z.im) == z;
  assert ComplexConj(ComplexConj(z)) == z;
}

/* helper modified by LLM (iteration 4): conjugation preserves squared norm */
lemma Conj_preserves_norm(z: Complex)
  ensures ComplexNormSq(ComplexConj(z)) == ComplexNormSq(z)
{
  assert ComplexConj(z) == Complex(z.re, -z.im);
  assert ComplexNormSq(ComplexConj(z)) == ComplexConj(z).re * ComplexConj(z).re + ComplexConj(z).im * ComplexConj(z).im;
  assert ComplexNormSq(ComplexConj(z)) == z.re * z.re + (-z.im) * (-z.im);
  assert (-z.im) * (-z.im) == z.im * z.im;
  assert ComplexNormSq(ComplexConj(z)) == z.re * z.re + z.im * z.im;
  assert ComplexNormSq(ComplexConj(z)) == ComplexNormSq(z);
}

/* helper modified by LLM (iteration 4): conjugation distributes over addition */
lemma Conj_add_distrib(z: Complex, y: Complex)
  ensures ComplexConj(ComplexAdd(z, y)) == ComplexAdd(ComplexConj(z), ComplexConj(y))
{
  assert ComplexAdd(z, y) == Complex(z.re + y.re, z.im + y.im);
  assert ComplexConj(ComplexAdd(z, y)) == Complex(z.re + y.re, -(z.im + y.im));
  assert ComplexConj(z) == Complex(z.re, -z.im);
  assert ComplexConj(y) == Complex(y.re, -y.im);
  assert ComplexAdd(ComplexConj(z), ComplexConj(y)) == Complex(z.re + y.re, -z.im + -y.im);
  assert -(z.im + y.im) == -z.im + -y.im;
  assert ComplexConj(ComplexAdd(z, y)) == ComplexAdd(ComplexConj(z), ComplexConj(y));
}

/* helper modified by LLM (iteration 4): conjugation distributes over multiplication */
lemma Conj_mul_distrib(z: Complex, y: Complex)
  ensures ComplexConj(ComplexMul(z, y)) == ComplexMul(ComplexConj(z), ComplexConj(y))
{
  assert ComplexMul(z, y) == Complex(z.re * y.re - z.im * y.im, z.re * y.im + z.im * y.re);
  assert ComplexConj(ComplexMul(z, y)) == Complex(z.re * y.re - z.im * y.im, -(z.re * y.im + z.im * y.re));
  assert ComplexConj(z) == Complex(z.re, -z.im);
  assert ComplexConj(y) == Complex(y.re, -y.im);
  assert ComplexMul(ComplexConj(z), ComplexConj(y)) ==
         Complex(z.re * y.re - (-z.im) * (-y.im), z.re * (-y.im) + (-z.im) * y.re);
  assert (-z.im) * (-y.im) == z.im * y.im;
  assert z.re * (-y.im) + (-z.im) * y.re == -(z.re * y.im + z.im * y.re);
  assert ComplexConj(ComplexMul(z, y)) == ComplexMul(ComplexConj(z), ComplexConj(y));
}

/* helper modified by LLM (iteration 4): preserves real numbers */
lemma Conj_real_preserve(z: Complex)
  ensures z.im == 0.0 ==> ComplexConj(z) == z
{
  if z.im == 0.0 {
    assert ComplexConj(z) == Complex(z.re, -z.im);
    assert -z.im == z.im;
    assert Complex(z.re, -z.im) == z;
    assert ComplexConj(z) == z;
  }
}

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
/* code modified by LLM (iteration 4): compute element-wise conjugate using loop with invariants */
{
  var i := 0;
  result := [];
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == ComplexConj(x[j])
  {
    result := result + [ComplexConj(x[i])];
    i := i + 1;
  }
}

// </vc-code>
