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
{
lemma HermiteBasis_zero()
  ensures forall x: real :: HermiteBasis(0,x) == 1.0
{
}

lemma HermiteBasis_one()
  ensures forall x: real :: HermiteBasis(1,x) == x
{
}

lemma HermiteBasis_rec(k: nat)
  requires k >= 2
  ensures forall x: real :: HermiteBasis(k,x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
  decreases k
{
  // Follows directly from the recursive definition of HermiteBasis
}

lemma HermiteBasisParity(k: nat)
  ensures forall x: real :: HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
  decreases k
{
  if k == 0 {
    // HermiteBasis(0, -x) == 1.0 == 1.0 * HermiteBasis(0, x)
  } else if k == 1 {
    // HermiteBasis(1, -x) == -x == -1.0 * HermiteBasis(1, x)
  } else {
    HermiteBasisParity(k-1);
    HermiteBasisParity(k-2);
    // Using the recursive definition and the inductive hypotheses gives the result for k
  }
}

lemma HermiteParityUpTo(n: nat)
  ensures forall k: nat, x: real :: k < n ==> HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
  decreases n
{
  if n == 0 {
    return;
  }
  HermiteParityUpTo(n-1);
  HermiteBasisParity(n-1);
}

lemma HermiteBasisPropsUpTo(n: nat)
  ensures forall k: nat {:trigger HermiteBasis(k, 0.0)} :: k < n ==> (
    (k == 0 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == 1.0) &&
    (k == 1 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x) &&
    (k >= 2 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x))
  )
  decreases n
{
  if n == 0 {
    return;
  }
  HermiteBasisPropsUpTo(n-1);
  var k := n - 1;
  if k == 0 {
    HermiteBasis_zero();
  } else if k == 1 {
    HermiteBasis_one();
  } else {
    HermiteBasis_rec(k);
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
  result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);
  // Prove parity property for all basis indices below the coefficient length
  HermiteParityUpTo(|coef|);
  // Prove the base and recurrence properties for all basis indices below the coefficient length
  HermiteBasisPropsUpTo(|coef|);
}

// </vc-code>
