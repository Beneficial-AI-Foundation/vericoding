// <vc-preamble>
// Custom datatype to represent float values that can be NaN
datatype FloatValue = NaN | Value(val: real)

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Predicate to check if there exists at least one non-NaN value in the sequence
predicate HasNonNaNValue(a: seq<FloatValue>) {
    exists i :: 0 <= i < |a| && !IsNaN(a[i])
}

// Predicate to check if all values in the sequence are NaN
predicate AllNaN(a: seq<FloatValue>) {
    forall i :: 0 <= i < |a| ==> IsNaN(a[i])
}

// Function to get all non-NaN values from the sequence
function GetNonNaNValues(a: seq<FloatValue>): seq<real>
{
    if |a| == 0 then []
    else if IsNaN(a[0]) then GetNonNaNValues(a[1..])
    else [a[0].val] + GetNonNaNValues(a[1..])
}

// Predicate to check if a value is the minimum among non-NaN elements
predicate IsMinOfNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists i :: 0 <= i < |a| && !IsNaN(a[i]) && result.val == a[i].val &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> result.val <= a[j].val))
}

// Predicate to check if a value is the maximum among non-NaN elements
predicate IsMaxOfNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists i :: 0 <= i < |a| && !IsNaN(a[i]) && result.val == a[i].val &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[j].val <= result.val))
}

// Predicate to check if result is bounded by non-NaN elements
predicate IsBoundedByNonNaN(a: seq<FloatValue>, result: FloatValue)
    requires HasNonNaNValue(a)
{
    !IsNaN(result) &&
    (exists min_i :: 0 <= min_i < |a| && !IsNaN(a[min_i]) &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[min_i].val <= a[j].val) &&
        a[min_i].val <= result.val) &&
    (exists max_i :: 0 <= max_i < |a| && !IsNaN(a[max_i]) &&
        (forall j :: 0 <= j < |a| && !IsNaN(a[j]) ==> a[j].val <= a[max_i].val) &&
        result.val <= a[max_i].val)
}

/**
 * Computes the q-th quantile of the data in a sequence, ignoring NaN values.
 * When all elements are NaN, returns NaN.
 * 
 * @param a: Input sequence of FloatValues (may contain NaN)
 * @param q: Quantile parameter, must be between 0.0 and 1.0 inclusive
 * @returns: The q-th quantile of non-NaN values, or NaN if all values are NaN
 */
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<real>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(a: seq<real>, x: real): (s: seq<real>)
    requires IsSorted(a)
    ensures IsSorted(s)
    ensures multiset(s) == multiset(a) + multiset{x}
{
    if a == [] then [x]
    else if x <= a[0] then [x] + a
    else [a[0]] + Insert(a[1..], x)
}

function Sort(a: seq<real>): (s: seq<real>)
    ensures IsSorted(s)
    ensures multiset(s) == multiset(a)
{
    if a == [] then []
    else Insert(Sort(a[1..]), a[0])
}

/* helper modified by LLM (iteration 5): fixed multiset comprehension syntax and added proof body */
lemma lemma_GetNonNaN_Properties(a: seq<FloatValue>)
    ensures AllNaN(a) <==> GetNonNaNValues(a) == []
    ensures multiset(GetNonNaNValues(a)) == multiset{ a[i].val | i: int | 0 <= i < |a| && !IsNaN(a[i]) }
{
    if |a| > 0 {
        lemma_GetNonNaN_Properties(a[1..]);
    }
}

lemma lemma_Sorted_Bounds(s: seq<real>)
    requires IsSorted(s) && |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[0] <= s[i] <= s[|s|-1]
{}

lemma lemma_Interpolation_Bounds(v1: real, v2: real, d: real)
    requires 0.0 <= d <= 1.0 && v1 <= v2
    ensures v1 <= v1 * (1.0 - d) + v2 * d <= v2
{}
// </vc-helpers>

// <vc-spec>
method nanquantile(a: seq<FloatValue>, q: real) returns (result: FloatValue)
    requires 0.0 <= q <= 1.0  // Quantile parameter must be valid
    requires |a| > 0           // Input sequence must be non-empty
    ensures
        // Case 1: If there exists at least one non-NaN element
        HasNonNaNValue(a) ==> 
            (IsBoundedByNonNaN(a, result) &&
             // For q=0, result is the minimum of non-NaN elements
             (q == 0.0 ==> IsMinOfNonNaN(a, result)) &&
             // For q=1, result is the maximum of non-NaN elements  
             (q == 1.0 ==> IsMaxOfNonNaN(a, result)))
    ensures
        // Case 2: If all elements are NaN, result is NaN
        AllNaN(a) ==> IsNaN(result)
    ensures
        // Case 3: For sequences without NaN, result is properly bounded
        (!exists i :: 0 <= i < |a| && IsNaN(a[i])) ==> 
            (!IsNaN(result) &&
             exists lower_i, upper_i :: 
                0 <= lower_i < |a| && 0 <= upper_i < |a| &&
                a[lower_i].val <= result.val <= a[upper_i].val)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Correcting compilation error was the priority. Logic unchanged. */
  var non_nan_values := GetNonNaNValues(a);

  lemma_GetNonNaN_Properties(a);
  if non_nan_values == [] {
    result := NaN;
  } else {
    var sorted_values := Sort(non_nan_values);
    var n := |sorted_values|;

    if n == 1 {
        result := Value(sorted_values[0]);
        return;
    }

    assert IsSorted(sorted_values);
    lemma_Sorted_Bounds(sorted_values);

    if q == 1.0 {
      result := Value(sorted_values[n-1]);
    } else {
      // Linear interpolation method
      var index_real := q * ((n - 1) as real);
      var k := index_real as int;
      assert 0.0 <= q < 1.0 ==> k < n - 1;
      var d := index_real - (k as real);
      var v1 := sorted_values[k];
      var v2 := sorted_values[k+1];
      
      lemma_Interpolation_Bounds(v1, v2, d);
      var quantile_val := v1 * (1.0 - d) + v2 * d;
      result := Value(quantile_val);
    }
  }
}
// </vc-code>
