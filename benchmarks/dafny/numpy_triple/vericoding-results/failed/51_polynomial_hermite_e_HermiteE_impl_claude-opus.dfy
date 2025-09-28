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
/* helper modified by LLM (iteration 5): Fixed lemmas to explicitly establish properties at trigger points */

// Lemma to prove the parity property of Hermite polynomials
lemma HermiteParityLemma(n: nat, x: real)
    ensures HermiteBasis(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x)
    decreases n
{
    if n == 0 {
        assert HermiteBasis(0, -x) == 1.0;
        assert HermiteBasis(0, x) == 1.0;
    } else if n == 1 {
        assert HermiteBasis(1, -x) == -x;
        assert HermiteBasis(1, x) == x;
    } else {
        HermiteParityLemma(n-1, x);
        HermiteParityLemma(n-2, x);
        
        var sign_n := if n % 2 == 0 then 1.0 else -1.0;
        var sign_n1 := if (n-1) % 2 == 0 then 1.0 else -1.0;
        var sign_n2 := if (n-2) % 2 == 0 then 1.0 else -1.0;
        
        calc {
            HermiteBasis(n, -x);
        ==
            (-x) * HermiteBasis(n-1, -x) - (n-1) as real * HermiteBasis(n-2, -x);
        ==
            (-x) * sign_n1 * HermiteBasis(n-1, x) - (n-1) as real * sign_n2 * HermiteBasis(n-2, x);
        ==
            -sign_n1 * x * HermiteBasis(n-1, x) - sign_n2 * (n-1) as real * HermiteBasis(n-2, x);
        == { assert sign_n == -sign_n1; assert sign_n == sign_n2; }
            sign_n * (x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x));
        ==
            sign_n * HermiteBasis(n, x);
        }
    }
}

// Establish parity property for polynomial
lemma EstablishParityProperty(coef: seq<real>)
    requires |coef| > 0
    ensures forall k: nat, x: real :: k < |coef| ==> 
        HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
{
    forall k: nat, x: real | k < |coef|
        ensures HermiteBasis(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * HermiteBasis(k, x)
    {
        HermiteParityLemma(k, x);
    }
}

// Lemma establishing base cases at trigger point 0.0
lemma EstablishBaseCasesAtZero(coef: seq<real>)
    requires |coef| > 0
    ensures forall k: nat :: k < |coef| ==>
        (k == 0 ==> HermiteBasis(k, 0.0) == 1.0) &&
        (k == 1 ==> HermiteBasis(k, 0.0) == 0.0)
{
    forall k: nat | k < |coef|
        ensures k == 0 ==> HermiteBasis(k, 0.0) == 1.0
        ensures k == 1 ==> HermiteBasis(k, 0.0) == 0.0
    {
        if k == 0 {
            assert HermiteBasis(0, 0.0) == 1.0;
        } else if k == 1 {
            assert HermiteBasis(1, 0.0) == 0.0;
        }
    }
}

// Lemma for base case properties for all x
lemma EstablishBaseCases(coef: seq<real>)
    requires |coef| > 0
    ensures forall k: nat :: k < |coef| ==>
        (k == 0 ==> forall x: real :: HermiteBasis(k, x) == 1.0) &&
        (k == 1 ==> forall x: real :: HermiteBasis(k, x) == x)
{
    forall k: nat | k < |coef|
        ensures k == 0 ==> forall x: real :: HermiteBasis(k, x) == 1.0
        ensures k == 1 ==> forall x: real :: HermiteBasis(k, x) == x
    {
        if k == 0 {
            forall x: real
                ensures HermiteBasis(k, x) == 1.0
            {
                assert HermiteBasis(0, x) == 1.0;
            }
        } else if k == 1 {
            forall x: real
                ensures HermiteBasis(k, x) == x
            {
                assert HermiteBasis(1, x) == x;
            }
        }
    }
}

// Lemma for recursive case at trigger point 0.0
lemma EstablishRecursiveCasesAtZero(coef: seq<real>)
    requires |coef| > 0
    ensures forall k: nat :: k >= 2 && k < |coef| ==>
        HermiteBasis(k, 0.0) == 0.0 * HermiteBasis(k-1, 0.0) - (k-1) as real * HermiteBasis(k-2, 0.0)
{
    forall k: nat | k >= 2 && k < |coef|
        ensures HermiteBasis(k, 0.0) == 0.0 * HermiteBasis(k-1, 0.0) - (k-1) as real * HermiteBasis(k-2, 0.0)
    {
        // This follows directly from the definition
    }
}

// Lemma for recursive case for all x
lemma EstablishRecursiveCases(coef: seq<real>)
    requires |coef| > 0
    ensures forall k: nat :: k >= 2 && k < |coef| ==>
        forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
{
    forall k: nat | k >= 2 && k < |coef|
        ensures forall x: real :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
    {
        forall x: real
            ensures HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x)
        {
            // This follows directly from the definition of HermiteBasis for k >= 2
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
/* code modified by LLM (iteration 5): Call lemmas with explicit trigger point establishment */
{
    result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);
    
    // Establish the parity property
    EstablishParityProperty(coef);
    
    // First establish properties at the trigger point 0.0
    EstablishBaseCasesAtZero(coef);
    EstablishRecursiveCasesAtZero(coef);
    
    // Then establish the full properties for all x
    EstablishBaseCases(coef);
    EstablishRecursiveCases(coef);
    
    // Explicitly assert the trigger-based postconditions
    assert forall k: nat {:trigger HermiteBasis(k, 0.0)} :: k < |coef| ==>
        (k == 0 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == 1.0) &&
        (k == 1 ==> forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x);
    
    assert forall k: nat {:trigger HermiteBasis(k, 0.0)} :: k >= 2 && k < |coef| ==>
        forall x: real {:trigger HermiteBasis(k, x)} :: HermiteBasis(k, x) == x * HermiteBasis(k-1, x) - (k-1) as real * HermiteBasis(k-2, x);
}
// </vc-code>
