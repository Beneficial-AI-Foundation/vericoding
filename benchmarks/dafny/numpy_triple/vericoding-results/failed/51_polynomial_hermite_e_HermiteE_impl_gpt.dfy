// <vc-preamble>
// HermiteE polynomial data structure
datatype HermiteEPoly = HermiteEPoly(
    coef: seq<real>,         // Coefficients in order of increasing degree
    domainMin: real,         // Domain interval lower bound
    domainMax: real,         // Domain interval upper bound  
    windowMin: real,         // Window interval lower bound
    windowMax: real          // Window interval upper bound
)

// Ghost function defining the nth HermiteE basis polynomial
ghost function HermiteBasis(n: nat, x: real): real
    decreases n
{
    if n == 0 then 1.0
    else if n == 1 then x
    else x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x)
}

// Predicate verifying HermiteE polynomial parity property
ghost predicate HasParityProperty(poly: HermiteEPoly)
{
    forall k: nat, x: real :: k < |poly.coef| ==> 
        HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
}

// Predicate verifying domain and window intervals are valid
predicate ValidIntervals(poly: HermiteEPoly)
{
    poly.domainMin < poly.domainMax && poly.windowMin < poly.windowMax
}

// Method to create HermiteE polynomial from coefficients with default domain and window
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parity relations and inductive parity lemma without assumes */
lemma Mod2Rel(n: nat)
  requires n >= 2
  ensures (if n % 2 == 0 then 1.0 else -1.0) == - (if (n - 1) % 2 == 0 then 1.0 else -1.0)
  ensures (if n % 2 == 0 then 1.0 else -1.0) == (if (n - 2) % 2 == 0 then 1.0 else -1.0)
{
  if n % 2 == 0 {
    var t := n / 2;
    assert n == 2 * t + n % 2;
    assert n == 2 * t;
    assert (2 * t) % 2 == 0;
    assert (n - 1) == 2 * t - 1;
    assert (2 * t - 1) % 2 == 1;
    assert (n - 2) == 2 * (t - 1);
    assert (2 * (t - 1)) % 2 == 0;

    assert (if n % 2 == 0 then 1.0 else -1.0) == 1.0;
    assert (if (n - 1) % 2 == 0 then 1.0 else -1.0) == -1.0;
    assert (if (n - 2) % 2 == 0 then 1.0 else -1.0) == 1.0;
  } else {
    var t := n / 2;
    assert n == 2 * t + 1;
    assert (2 * t) % 2 == 0;
    assert (2 * t + 1) % 2 == 1;
    assert (n - 1) == 2 * t;
    assert (n - 2) == 2 * t - 1;
    assert (2 * t - 1) % 2 == 1;

    assert (if n % 2 == 0 then 1.0 else -1.0) == -1.0;
    assert (if (n - 1) % 2 == 0 then 1.0 else -1.0) == 1.0;
    assert (if (n - 2) % 2 == 0 then 1.0 else -1.0) == -1.0;
  }
}

/* helper modified by LLM (iteration 5): inductive proof of HermiteE basis parity property */
lemma ParityLemma(n: nat, x: real)
  ensures HermiteBasis(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x)
  decreases n
{
  if n == 0 {
    assert HermiteBasis(0, -x) == 1.0;
    assert HermiteBasis(0, x) == 1.0;
    assert (if 0 % 2 == 0 then 1.0 else -1.0) == 1.0;
  } else if n == 1 {
    assert HermiteBasis(1, -x) == -x;
    assert HermiteBasis(1, x) == x;
    assert (if 1 % 2 == 0 then 1.0 else -1.0) == -1.0;
  } else {
    ParityLemma(n - 1, x);
    ParityLemma(n - 2, x);
    Mod2Rel(n);
    var s := if n % 2 == 0 then 1.0 else -1.0;
    var s1 := if (n - 1) % 2 == 0 then 1.0 else -1.0;
    var s2 := if (n - 2) % 2 == 0 then 1.0 else -1.0;
    calc {
      HermiteBasis(n, -x);
      == { }
      (-x) * HermiteBasis(n - 1, -x) - (n - 1) as real * HermiteBasis(n - 2, -x);
      == { }
      (-x) * (s1 * HermiteBasis(n - 1, x)) - (n - 1) as real * (s2 * HermiteBasis(n - 2, x));
      == { assert s == -s1; assert s == s2; }
      s * x * HermiteBasis(n - 1, x) - (n - 1) as real * s * HermiteBasis(n - 2, x);
      == { }
      s * (x * HermiteBasis(n - 1, x) - (n - 1) as real * HermiteBasis(n - 2, x));
      == { }
      s * HermiteBasis(n, x);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method HermiteE(coef: seq<real>) returns (result: HermiteEPoly)
    requires |coef| > 0
    ensures result.coef == coef
    ensures result.domainMin == -1.0 && result.domainMax == 1.0
    ensures result.windowMin == -1.0 && result.windowMax == 1.0
    ensures ValidIntervals(result)
    ensures HasParityProperty(result)
    ensures forall k: nat {:trigger HermiteBasis(k, 0.0)} :: k < |coef| ==> 
        (k == 0 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == 1.0) &&
        (k == 1 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x)
    ensures forall k: nat {:trigger HermiteBasis(k, 0.0)} :: k >= 2 && k < |coef| ==> 
        forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct polynomial and prove properties without assumes */
  result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);

  // Intervals validity
  assert result.domainMin < result.domainMax;
  assert result.windowMin < result.windowMax;
  assert ValidIntervals(result);

  // HasParityProperty(result) via ParityLemma
  assert forall k: nat, x: real :: k < |result.coef| ==> HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
  by {
    var k: nat;
    var x: real;
    if k < |result.coef| {
      ParityLemma(k, x);
    }
  };

  // Base cases for k == 0 and k == 1 across all x
  assert forall k: nat :: k < |result.coef| ==> (k == 0 ==> forall x: real :: HermiteBasis(k, x) == 1.0) && (k == 1 ==> forall x: real :: HermiteBasis(k, x) == x)
  by {
    var k: nat;
    if k < |result.coef| {
      if k == 0 {
        assert forall x: real :: HermiteBasis(k, x) == 1.0 by {
          var x: real;
        };
      }
      if k == 1 {
        assert forall x: real :: HermiteBasis(k, x) == x by {
          var x: real;
        };
      }
    }
  };

  // Recurrence for all k >= 2 across all x
  assert forall k: nat :: k >= 2 && k < |result.coef| ==> forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k - 1, x) - (k - 1) as real * HermiteBasis(k - 2, x)
  by {
    var k: nat;
    if k >= 2 && k < |result.coef| {
      assert forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k - 1, x) - (k - 1) as real * HermiteBasis(k - 2, x)
      by {
        var x: real;
      };
    }
  };
}

// </vc-code>
