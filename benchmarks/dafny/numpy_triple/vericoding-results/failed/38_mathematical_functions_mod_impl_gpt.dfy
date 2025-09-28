// <vc-preamble>
// Method to compute element-wise modulo operation on fixed-size vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define modulo for reals using floor decomposition */
function FMod(a: real, b: real): real
  requires b != 0.0
{
  a - ((a / b).Floor as real) * b
}

/* helper modified by LLM (iteration 5): lemma for decomposition a = floor(a/b)*b + FMod(a,b) */
lemma FModDecomp(a: real, b: real)
  requires b != 0.0
  ensures a == ((a / b).Floor as real) * b + FMod(a, b)
{
  calc {
    a;
    == { }
    ((a / b).Floor as real) * b + (a - ((a / b).Floor as real) * b);
    == { assert FMod(a, b) == a - ((a / b).Floor as real) * b; }
    ((a / b).Floor as real) * b + FMod(a, b);
  }
}

/* helper modified by LLM (iteration 5): prove bounds for FMod based on sign of divisor */
lemma FModBounds(a: real, b: real)
  requires b != 0.0
  ensures b > 0.0 ==> 0.0 <= FMod(a, b) && FMod(a, b) < b
  ensures b < 0.0 ==> FMod(a, b) <= 0.0 && FMod(a, b) > b
{
  var q: int := (a / b).Floor;
  var qr: real := q as real;
  assert qr <= a / b;
  assert a / b < qr + 1.0;

  if b > 0.0 {
    assert qr * b <= a;
    assert a < (qr + 1.0) * b;
    assert FMod(a, b) == a - qr * b;
    assert 0.0 <= a - qr * b;
    assert a - qr * b < b;
  } else {
    assert qr * b >= a;
    assert a > (qr + 1.0) * b;
    assert FMod(a, b) == a - qr * b;
    assert a - qr * b <= 0.0;
    assert a - qr * b > b;
  }
}

// </vc-helpers>

// <vc-spec>
method numpy_mod(n: nat, x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Precondition: vectors must have fixed length n and all divisors must be non-zero
  requires |x1| == n && |x2| == n
  requires forall i :: 0 <= i < |x2| ==> x2[i] != 0.0
  
  // Postcondition: result has same fixed length as inputs
  ensures |result| == n
  
  // Postcondition: each element satisfies the mathematical remainder properties
  // (approximating floating-point floor behavior with real floor)
  ensures forall i :: 0 <= i < |result| ==>
    var r := result[i];
    var a := x1[i];
    var b := x2[i];
    // Basic remainder property: a = floor(a/b) * b + r
    a == (a / b).Floor as real * b + r &&
    // Result has same sign as divisor and proper bounds
    (b > 0.0 ==> r >= 0.0 && r < b) &&
    (b < 0.0 ==> r <= 0.0 && r > b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fix reserved identifier usage and construct result with proofs */
  var res: seq<real> := [];
  var i: nat := 0;
  while i < n
    invariant 0 <= i && i <= n
    invariant |x1| == n && |x2| == n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == FMod(x1[j], x2[j])
  {
    assert i < |x1| && i < |x2|;
    var r := FMod(x1[i], x2[i]);
    FModBounds(x1[i], x2[i]);
    var prev: seq<real> := res;
    res := prev + [r];
    assert forall j :: 0 <= j < i + 1 ==> res[j] == FMod(x1[j], x2[j]) by {
      if j < i {
        assert j < |prev|;
        assert res[j] == prev[j];
        assert prev[j] == FMod(x1[j], x2[j]);
      } else {
        assert j == i;
        assert res[j] == r;
        assert r == FMod(x1[j], x2[j]);
      }
    };
    i := i + 1;
  }
  result := res;
  assert |result| == n;

  assert forall k :: 0 <= k < |result| ==> 
    (x1[k] == ((x1[k] / x2[k]).Floor as real) * x2[k] + result[k]) &&
    (x2[k] > 0.0 ==> 0.0 <= result[k] && result[k] < x2[k]) &&
    (x2[k] < 0.0 ==> result[k] <= 0.0 && result[k] > x2[k])
  by {
    assert |result| == n && |x2| == n;
    assert result == res;
    assert 0 <= k && k < n;
    assert result[k] == res[k];
    assert res[k] == FMod(x1[k], x2[k]);

    calc {
      x1[k];
      == { FModDecomp(x1[k], x2[k]); }
      ((x1[k] / x2[k]).Floor as real) * x2[k] + FMod(x1[k], x2[k]);
      == { assert result[k] == FMod(x1[k], x2[k]); }
      ((x1[k] / x2[k]).Floor as real) * x2[k] + result[k];
    }

    FModBounds(x1[k], x2[k]);
    if x2[k] > 0.0 {
      assert 0.0 <= FMod(x1[k], x2[k]) && FMod(x1[k], x2[k]) < x2[k];
      assert 0.0 <= result[k] && result[k] < x2[k];
    } else if x2[k] < 0.0 {
      assert FMod(x1[k], x2[k]) <= 0.0 && FMod(x1[k], x2[k]) > x2[k];
      assert result[k] <= 0.0 && result[k] > x2[k];
    }
  };
}
// </vc-code>
