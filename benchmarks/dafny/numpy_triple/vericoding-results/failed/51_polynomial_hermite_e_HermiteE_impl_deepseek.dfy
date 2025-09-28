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
/* helper modified by LLM (iteration 5): Fixed lemma to properly handle parity proof with complete forall quantification */

// Helper lemma to prove the parity property of Hermite basis polynomials
lemma HermiteBasisParityLemma(n: nat)
    ensures forall x: real :: HermiteBasis(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x)
    decreases n
{
    if n == 0 {
        // Base case n=0: H₀(-x) = 1 = 1 * H₀(x)
    } else if n == 1 {
        // Base case n=1: H₁(-x) = -x = -1 * H₁(x)
    } else {
        // Inductive step: assume parity holds for n-1 and n-2
        HermiteBasisParityLemma(n-1);
        HermiteBasisParityLemma(n-2);
        
        // Prove for all x
        forall x: real {
            calc {
                HermiteBasis(n, -x);
                == {}
                (-x) * HermiteBasis(n-1, -x) - (n-1) as real * HermiteBasis(n-2, -x);
                == { HermiteBasisParityLemma(n-1); HermiteBasisParityLemma(n-2); }
                (-x) * ((if (n-1) % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n-1, x)) - 
                (n-1) as real * ((if (n-2) % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n-2, x));
                ==
                (if n % 2 == 0 then 1.0 else -1.0) * (x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x));
                == {}
                (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x);
            }
        }
    }
}

// Helper lemma to prove the definition properties of Hermite basis polynomials
lemma HermiteBasisDefinitionLemma(k: nat)
    ensures (k == 0 ==> forall x: real :: HermiteBasis(k, x) == 1.0) &&
            (k == 1 ==> forall x: real :: HermiteBasis(k, x) == x) &&
            (k >= 2 ==> forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x))
{
    // The properties follow directly from the definition of HermiteBasis function
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
/* code modified by LLM (iteration 5): Complete implementation proving all postconditions without verification bypasses */
{
  result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);
  
  // Prove ValidIntervals
  assert result.domainMin == -1.0 && result.domainMax == 1.0 && result.windowMin == -1.0 && result.windowMax == 1.0;
  assert ValidIntervals(result);
  
  // Prove HasParityProperty using lemma
  var k: nat := 0;
  while k < |coef|
    invariant k <= |coef|
    invariant forall i: nat :: i < k ==> (forall x: real :: HermiteBasis(i, -x) == (if i % 2 == 0 then 1.0 else -1.0) * HermiteBasis(i, x))
  {
    HermiteBasisParityLemma(k);
    k := k + 1;
  }
  
  // Prove the definition properties
  k := 0;
  while k < |coef|
    invariant k <= |coef|
    invariant forall i: nat :: i < k ==> 
        (i == 0 ==> forall x: real :: HermiteBasis(i, x) == 1.0) &&
        (i == 1 ==> forall x: real :: HermiteBasis(i, x) == x) &&
        (i >= 2 ==> forall x: real :: HermiteBasis(i, x) == x * HermiteBasis(i-1, x) - (i-1) as real * HermiteBasis(i-2, x))
  {
    HermiteBasisDefinitionLemma(k);
    k := k + 1;
  }
}
// </vc-code>
