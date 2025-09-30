// <vc-preamble>

datatype Value = IntVal(i: int) | BoolVal(b: bool) | StringVal(s: string) | RealVal(r: real) | OtherVal

predicate ValidInput(values: seq<Value>)
{
    true  // All sequences of Value are valid input
}

function IntegerValues(values: seq<Value>) : seq<int>
{
    if |values| == 0 then []
    else 
        match values[0]
        case IntVal(i) => [i] + IntegerValues(values[1..])
        case BoolVal(b) => [if b then 1 else 0] + IntegerValues(values[1..])
        case _ => IntegerValues(values[1..])
}

predicate ValidOutput(input: seq<Value>, output: seq<int>)
{
    output == IntegerValues(input)
}
// </vc-preamble>

// <vc-helpers>
lemma IntegerValuesCorrectness(values: seq<Value>)
    ensures |IntegerValues(values)| <= |values|
    ensures forall x :: x in IntegerValues(values) ==>
        exists i :: 0 <= i < |values| && (values[i] == IntVal(x) || (values[i].BoolVal? && x == (if values[i].b then 1 else 0)))
    ensures forall i :: 0 <= i < |values| && values[i].IntVal? ==> values[i].i in IntegerValues(values)
    ensures forall i :: 0 <= i < |values| && values[i].BoolVal? ==> (if values[i].b then 1 else 0) in IntegerValues(values)
{
    if |values| == 0 {
        // Base case
    } else {
        IntegerValuesCorrectness(values[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method filter_integers(values: seq<Value>) returns (result: seq<int>)
    requires ValidInput(values)
    ensures ValidOutput(values, result)
    ensures |result| <= |values|
    ensures forall x :: x in result ==> 
        exists i :: 0 <= i < |values| && (values[i] == IntVal(x) || (values[i].BoolVal? && x == (if values[i].b then 1 else 0)))
    ensures forall i :: 0 <= i < |values| && values[i].IntVal? ==> values[i].i in result
    ensures forall i :: 0 <= i < |values| && values[i].BoolVal? ==> (if values[i].b then 1 else 0) in result
// </vc-spec>
// <vc-code>
{
    IntegerValuesCorrectness(values);
    result := IntegerValues(values);
}
// </vc-code>
