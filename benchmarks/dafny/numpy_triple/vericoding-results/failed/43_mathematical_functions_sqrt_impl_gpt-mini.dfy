// <vc-preamble>
// Float datatype that can represent NaN for negative inputs
datatype Float = Real(value: real) | NaN

// Vector represented as a sequence with a fixed length
datatype Vector<T> = Vector(elements: seq<T>, length: nat)
{
    predicate Valid() {
        |elements| == length
    }
    
    function get(i: nat): T
        requires Valid()
        requires i < length
    {
        elements[i]
    }
}

// Helper predicate to check if a Float is non-negative
predicate NonNegative(x: Float) {
    x.Real? && x.value >= 0.0
}

// Helper predicate to check if a Float is NaN
predicate IsNaN(x: Float) {
    x.NaN?
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): monotonicity lemma for non-negative square roots */
lemma sqrt_monotone(a: real, b: real, y1: real, y2: real)
  requires 0.0 <= a <= b
  requires y1*y1 == a && y1 >= 0.0
  requires y2*y2 == b && y2 >= 0.0
  ensures y1 <= y2
{
  if y1 > y2 {
    assert y1 - y2 > 0.0;
    assert y2 >= 0.0;
    // from y1 > y2 and y2 >= 0 we get y1 > 0
    assert y1 > 0.0;
    // hence the sum is strictly positive
    assert y1 + y2 > 0.0;
    assert (y1 - y2) * (y1 + y2) > 0.0;
    assert y1*y1 > y2*y2;
    assert a > b;
    assert false;
  }
}

// </vc-helpers>

// <vc-spec>
method sqrt(x: Vector<Float>) returns (result: Vector<Float>)
    requires x.Valid()
    ensures result.Valid()
    ensures result.length == x.length
    // For non-negative inputs: result² = input and result ≥ 0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value >= 0.0 ==>
        result.get(i).Real? && result.get(i).value * result.get(i).value == x.get(i).value && result.get(i).value >= 0.0
    // For negative inputs: result is NaN
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value < 0.0 ==>
        result.get(i).NaN?
    // NaN inputs produce NaN outputs
    ensures forall i :: 0 <= i < x.length && x.get(i).NaN? ==>
        result.get(i).NaN?
    // Special cases
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 0.0 ==>
        result.get(i).Real? && result.get(i).value == 0.0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 1.0 ==>
        result.get(i).Real? && result.get(i).value == 1.0
    // Monotonicity on non-negative inputs
    ensures forall i, j :: (0 <= i < x.length && 0 <= j < x.length &&
        x.get(i).Real? && x.get(j).Real? && 
        x.get(i).value >= 0.0 && x.get(j).value >= 0.0 && x.get(i).value <= x.get(j).value) ==>
        result.get(i).Real? && result.get(j).Real? && result.get(i).value <= result.get(j).value
    // Shape preservation is guaranteed by the length equality
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): elementwise sqrt using witness y for non-negative reals */
  var outElems : seq<Float> := [];
  var i := 0;
  while i < x.length
    invariant 0 <= i <= x.length
    invariant |outElems| == i
    invariant forall k :: 0 <= k < |outElems| ==>
      (if x.get(k).Real? then
         if x.get(k).value >= 0.0 then outElems[k].Real? && outElems[k].value * outElems[k].value == x.get(k).value && outElems[k].value >= 0.0
         else outElems[k].NaN?
       else outElems[k].NaN?)
  {
    var xi := x.get(i);
    if xi.NaN? {
      outElems := outElems + [NaN];
    } else if xi.Real? && xi.value < 0.0 {
      outElems := outElems + [NaN];
    } else {
      // witness y such that y*y == xi.value and y >= 0.0
      var y :| y * y == xi.value && y >= 0.0;
      outElems := outElems + [Real(y)];
    }
    i := i + 1;
  }
  result := Vector(outElems, x.length);

  // Ghost proof to establish monotonicity on non-negative inputs
  ghost var ii := 0;
  while ii < x.length
    invariant 0 <= ii <= x.length
  {
    ghost var jj := 0;
    while jj < x.length
      invariant 0 <= jj <= x.length
    {
      if x.get(ii).Real? && x.get(jj).Real? && x.get(ii).value >= 0.0 && x.get(jj).value >= 0.0 && x.get(ii).value <= x.get(jj).value {
        assert result.get(ii) == outElems[ii];
        assert result.get(jj) == outElems[jj];
        assert result.get(ii).Real?;
        assert result.get(jj).Real?;
        var yi := result.get(ii).value;
        var yj := result.get(jj).value;
        assert yi*yi == x.get(ii).value;
        assert yj*yj == x.get(jj).value;
        sqrt_monotone(x.get(ii).value, x.get(jj).value, yi, yj);
      }
      jj := jj + 1;
    }
    ii := ii + 1;
  }
}

// </vc-code>
