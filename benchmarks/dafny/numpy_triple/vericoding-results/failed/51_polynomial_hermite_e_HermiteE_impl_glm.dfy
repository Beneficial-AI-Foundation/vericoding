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
/* helper modified by LLM (iteration 3): Added base case lemmas and recurrence lemma */
lemma HermiteBasis0()
    ensures forall x: real :: HermiteBasis(0, x) == 1.0
{
    forall x: real 
        ensures HermiteBasis(0, x) == 1.0
    {
        calc {
            HermiteBasis(0, x);
            1.0;
        }
    }
}

/* helper modified by LLM (iteration 3): Added base case lemmas and recurrence lemma */
lemma HermiteBasis1()
    ensures forall x: real :: HermiteBasis(1, x) == x
{
    forall x: real 
        ensures HermiteBasis(1, x) == x
    {
        calc {
            HermiteBasis(1, x);
            x;
        }
    }
}

/* helper modified by LLM (iteration 3): Added base case lemmas and recurrence lemma */
lemma HermiteBasisRecurrence(n: nat)
    requires n >= 2
    ensures forall x: real :: HermiteBasis(n, x) == x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x)
{
    forall x: real 
        ensures HermiteBasis(n, x) == x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x)
    {
        calc {
            HermiteBasis(n, x);
            { reveal HermiteBasis(); }
            x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x);
        }
    }
}

/* helper modified by LLM (iteration 3): Fixed n>=2 case by removing square brackets and defining sign_n properly */
lemma HermiteBasisParity(n: nat)
    ensures forall x: real :: HermiteBasis(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x)
{
    if n == 0 {
        forall x: real 
            ensures HermiteBasis(0, -x) == (if 0 % 2 == 0 then 1.0 else -1.0) * HermiteBasis(0, x)
        {
            calc {
                HermiteBasis(0, -x);
                1.0;
                (if 0 % 2 == 0 then 1.0 else -1.0) * HermiteBasis(0, x);
                1.0 * 1.0;
                1.0;
            }
        }
    } else if n == 1 {
        forall x: real 
            ensures HermiteBasis(1, -x) == (if 1 % 2 == 0 then 1.0 else -1.0) * HermiteBasis(1, x)
        {
            calc {
                HermiteBasis(1, -x);
                -x;
                (if 1 % 2 == 0 then 1.0 else -1.0) * HermiteBasis(1, x);
                -1.0 * x;
                -x;
            }
        }
    } else {
        HermiteBasisParity(n-1);
        HermiteBasisParity(n-2);
        forall x: real 
            ensures HermiteBasis(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n, x)
        {
            var sign_n := if n % 2 == 0 then 1.0 else -1.0;
            calc {
                HermiteBasis(n, -x);
                { reveal HermiteBasis(); }
                (-x) * HermiteBasis(n-1, -x) - (n-1) as real * HermiteBasis(n-2, -x);
                { HermiteBasisParity(n-1); HermiteBasisParity(n-2); }
                (-x) * ((if (n-1) % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n-1, x)) - (n-1) as real * ((if (n-2) % 2 == 0 then 1.0 else -1.0) * HermiteBasis(n-2, x));
                assert (if (n-1) % 2 == 0 then 1.0 else -1.0) == -sign_n;
                assert (if (n-2) % 2 == 0 then 1.0 else -1.0) == sign_n;
                (-x) * (-sign_n * HermiteBasis(n-1, x)) - (n-1) as real * (sign_n * HermiteBasis(n-2, x));
                { calc {
                    (-x) * (-sign_n * HermiteBasis(n-1, x)) - (n-1) as real * (sign_n * HermiteBasis(n-2, x));
                    sign_n * (x * HermiteBasis(n-1, x) - (n-1) as real * HermiteBasis(n-2, x));
                }}
                { HermiteBasisRecurrence(n); }
                sign_n * HermiteBasis(n, x);
            }
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
  /* code modified by LLM (iteration 3): Updated to use newly defined base case and recurrence lemmas */
  result := HermiteEPoly(coef, -1.0, 1.0, -1.0, 1.0);
  var n := |coef|;
  if n > 0 {
    HermiteBasis0();
    HermiteBasisParity(0);
  }
  if n > 1 {
    HermiteBasis1();
    HermiteBasisParity(1);
  }
  for k := 2 to n-1 {
    HermiteBasisRecurrence(k);
    HermiteBasisParity(k);
  }
}
// </vc-code>
