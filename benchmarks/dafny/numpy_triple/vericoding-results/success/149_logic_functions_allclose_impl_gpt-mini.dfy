// <vc-preamble>
// Helper function to compute absolute value
function Abs(x: real): real
{
    if x >= 0.0 then x else -x
}

// Main method implementing allclose functionality
// </vc-preamble>

// <vc-helpers>
predicate CloseElem(x: real, y: real, rtol: real, atol: real) { Abs(x - y) <= atol + rtol * Abs(y) }
// </vc-helpers>

// <vc-spec>
method allclose(a: seq<real>, b: seq<real>, rtol: real, atol: real) returns (result: bool)
    // Preconditions: tolerance values must be non-negative and sequences must have same length
    requires rtol >= 0.0
    requires atol >= 0.0
    requires |a| == |b|
    
    // Postcondition: result is true iff all elements satisfy the tolerance condition
    // For each element i: abs(a[i] - b[i]) <= atol + rtol * abs(b[i])
    ensures result == (forall i :: 0 <= i < |a| ==> 
        Abs(a[i] - b[i]) <= atol + rtol * Abs(b[i]))
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var i := 0;
  result := true;
  while i < n
    invariant 0 <= i <= n
    invariant result == (forall j :: 0 <= j < i ==> Abs(a[j] - b[j]) <= atol + rtol * Abs(b[j]))
    decreases n - i
  {
    if !(Abs(a[i] - b[i]) <= atol + rtol * Abs(b[i])) {
      result := false;
    }
    i := i + 1;
  }
}

// </vc-code>
