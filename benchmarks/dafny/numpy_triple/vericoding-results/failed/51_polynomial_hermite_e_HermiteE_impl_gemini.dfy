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
/* helper modified by LLM (iteration 5): [retained correct helpers from previous turn, no changes made] */
lemma {:induction k} HermiteBasisParityLemma(k: nat, x: real)
  ensures HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
{
  if k >= 2 {
    HermiteBasisParityLemma(k-1, x);
    HermiteBasisParityLemma(k-2, x);
  }
}

lemma RevealHermiteBasis(k: nat, x: real)
    ensures k == 0 ==> HermiteBasis(k, x) == 1.0
    ensures k == 1 ==> HermiteBasis(k, x) == x
    ensures k >= 2 ==> HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
{
    // This lemma's body is empty. It serves to reveal the definition of HermiteBasis
    // to the verifier on demand. The verifier proves the ensures clauses by one-step unfolding.
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
  /* code modified by LLM (iteration 5): [added ensures clauses to inner forall to propagate proofs] */
  result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);

  forall k: nat | k < |coef|
    ensures forall x: real :: HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
    ensures (k == 0 ==> forall x: real :: HermiteBasis(k, x) == 1.0) &&
            (k == 1 ==> forall x: real :: HermiteBasis(k, x) == x)
    ensures k >= 2 ==> forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
  {
      forall x: real
        ensures HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
        ensures (k == 0 ==> HermiteBasis(k, x) == 1.0) &&
                (k == 1 ==> HermiteBasis(k, x) == x)
        ensures k >= 2 ==> HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
      {
          HermiteBasisParityLemma(k, x);
          RevealHermiteBasis(k, x);
      }
  }
}
// </vc-code>
