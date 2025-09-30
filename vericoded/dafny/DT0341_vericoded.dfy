// <vc-preamble>
// Datatype to represent floating point values that may be NaN
datatype FloatValue = NaN | Real(value: real)

// Helper predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
    f.NaN?
}

// Helper function to get the real value, treating NaN as 1.0
function GetValueOrOne(f: FloatValue): real
{
    if f.NaN? then 1.0 else f.value
}

// Helper function to compute product of non-NaN elements up to position i
function CumulativeProduct(arr: seq<FloatValue>, i: nat): real
    requires i < |arr|
{
    if i == 0 then
        GetValueOrOne(arr[0])
    else
        CumulativeProduct(arr, i-1) * GetValueOrOne(arr[i])
}

// Helper predicate to check if all elements up to position i are NaN
predicate AllNaNUpTo(arr: seq<FloatValue>, i: nat)
    requires i < |arr|
{
    forall j :: 0 <= j <= i ==> IsNaN(arr[j])
}

// Main method specification for nancumprod
// </vc-preamble>

// <vc-helpers>
// Helper lemma to prove cumulative product equivalence when all elements up to i are NaN
lemma CumulativeProductAllNaN(arr: seq<FloatValue>, i: nat)
    requires i < |arr|
    requires AllNaNUpTo(arr, i)
    ensures CumulativeProduct(arr, i) == 1.0
{
    if i == 0 {
        // Base case: CumulativeProduct(arr, 0) = GetValueOrOne(arr[0]) = 1.0 since arr[0] is NaN
    } else {
        // Inductive case: use the fact that arr[i] is NaN and all previous elements are NaN
        CumulativeProductAllNaN(arr, i-1);
    }
}

// Helper lemma to establish the relationship between AllNaNUpTo and CumulativeProduct
lemma CumulativeProductProperties(arr: seq<FloatValue>, i: nat)
    requires i < |arr|
    ensures AllNaNUpTo(arr, i) ==> CumulativeProduct(arr, i) == 1.0
{
    if AllNaNUpTo(arr, i) {
        CumulativeProductAllNaN(arr, i);
    }
}

/* helper modified by LLM (iteration 2): added lemma to prove postcondition implications */
lemma PostconditionHelper(arr: seq<FloatValue>, result: seq<FloatValue>)
    requires |result| == |arr|
    requires forall j :: 0 <= j < |arr| ==> result[j] == Real(CumulativeProduct(arr, j))
    ensures forall i :: 0 <= i < |arr| ==>
        (AllNaNUpTo(arr, i) ==> result[i] == Real(1.0)) &&
        (!AllNaNUpTo(arr, i) ==> result[i] == Real(CumulativeProduct(arr, i))) &&
        !IsNaN(result[i])
{
    forall i | 0 <= i < |arr|
        ensures (AllNaNUpTo(arr, i) ==> result[i] == Real(1.0)) &&
                (!AllNaNUpTo(arr, i) ==> result[i] == Real(CumulativeProduct(arr, i))) &&
                !IsNaN(result[i])
    {
        CumulativeProductProperties(arr, i);
        if AllNaNUpTo(arr, i) {
            assert CumulativeProduct(arr, i) == 1.0;
            assert result[i] == Real(CumulativeProduct(arr, i)) == Real(1.0);
        }
        assert result[i] == Real(CumulativeProduct(arr, i));
        assert !IsNaN(result[i]);
    }
}
// </vc-helpers>

// <vc-spec>
method NanCumprod(arr: seq<FloatValue>) returns (result: seq<FloatValue>)
    ensures |result| == |arr|
    ensures forall i :: 0 <= i < |arr| ==>
        // If all elements from start to i are NaN, result[i] = 1.0
        (AllNaNUpTo(arr, i) ==> result[i] == Real(1.0)) &&
        // Otherwise, result[i] = cumulative product treating NaN as 1.0
        (!AllNaNUpTo(arr, i) ==> result[i] == Real(CumulativeProduct(arr, i))) &&
        // Result is never NaN (since NaN is treated as 1.0)
        !IsNaN(result[i])
    ensures forall i :: 0 <= i < |arr| ==>
        // General property: each result element is the product of non-NaN elements up to that position
        result[i] == Real(CumulativeProduct(arr, i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added postcondition helper call */
    result := [];
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == Real(CumulativeProduct(arr, j))
        invariant forall j :: 0 <= j < i ==> !IsNaN(result[j])
    {
        CumulativeProductProperties(arr, i);
        var productValue := CumulativeProduct(arr, i);
        result := result + [Real(productValue)];
        i := i + 1;
    }
    
    PostconditionHelper(arr, result);
}
// </vc-code>
