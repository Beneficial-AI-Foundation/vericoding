// <vc-preamble>
// Datatype to represent floating point values including NaN
datatype FloatValue = Finite(value: real) | NaN

// Predicate to check if a value is NaN
predicate IsNaN(f: FloatValue) {
    f.NaN?
}

// Predicate to check if a value is finite (not NaN)
predicate IsFinite(f: FloatValue) {
    f.Finite?
}

// Extract the real value from a finite FloatValue
function GetValue(f: FloatValue): real
    requires IsFinite(f)
{
    f.value
}

// Check if there exists at least one non-NaN element in the sequence
predicate HasValidElements(a: seq<FloatValue>) {
    exists i :: 0 <= i < |a| && IsFinite(a[i])
}

// Check if all elements in the sequence are NaN
predicate AllNaN(a: seq<FloatValue>) {
    forall i :: 0 <= i < |a| ==> IsNaN(a[i])
}

// Count the number of non-NaN elements
function CountValidElements(a: seq<FloatValue>): nat {
    if |a| == 0 then 0
    else (if IsFinite(a[0]) then 1 else 0) + CountValidElements(a[1..])
}

// Sum all non-NaN elements
function SumValidElements(a: seq<FloatValue>): real {
    if |a| == 0 then 0.0
    else (if IsFinite(a[0]) then GetValue(a[0]) else 0.0) + SumValidElements(a[1..])
}

// Get the minimum value among non-NaN elements
function MinValidElement(a: seq<FloatValue>): real
    requires HasValidElements(a)
{
    if |a| == 1 then GetValue(a[0])
    else if IsFinite(a[0]) then
        if HasValidElements(a[1..]) then
            if GetValue(a[0]) <= MinValidElement(a[1..]) then GetValue(a[0])
            else MinValidElement(a[1..])
        else GetValue(a[0])
    else MinValidElement(a[1..])
}

// Get the maximum value among non-NaN elements  
function MaxValidElement(a: seq<FloatValue>): real
    requires HasValidElements(a)
{
    if |a| == 1 then GetValue(a[0])
    else if IsFinite(a[0]) then
        if HasValidElements(a[1..]) then
            if GetValue(a[0]) >= MaxValidElement(a[1..]) then GetValue(a[0])
            else MaxValidElement(a[1..])
        else GetValue(a[0])
    else MaxValidElement(a[1..])
}

// Main method: Compute the arithmetic mean while ignoring NaN values
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanmean(a: seq<FloatValue>) returns (result: FloatValue)
    ensures
        // Case 1: If there exists at least one non-NaN element, result is their arithmetic mean
        HasValidElements(a) ==> (
            IsFinite(result) &&
            GetValue(result) == SumValidElements(a) / (CountValidElements(a) as real)
        )
    ensures
        // Case 2: If all elements are NaN, result is NaN
        AllNaN(a) ==> IsNaN(result)
    ensures
        // Case 3: Result is never NaN when valid elements exist
        HasValidElements(a) ==> IsFinite(result)
    ensures
        // Case 4: For empty sequence, result is NaN
        |a| == 0 ==> IsNaN(result)
    ensures
        // Case 5: Result is bounded by min and max of non-NaN elements (when valid elements exist)
        HasValidElements(a) && IsFinite(result) ==> (
            MinValidElement(a) <= GetValue(result) <= MaxValidElement(a)
        )
    ensures
        // Case 6: For sequences without NaN, behaves like regular mean
        (forall i :: 0 <= i < |a| ==> IsFinite(a[i])) && |a| > 0 ==> (
            IsFinite(result) &&
            GetValue(result) == SumValidElements(a) / (|a| as real)
        )
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
