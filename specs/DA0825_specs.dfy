// <vc-preamble>

datatype Operation = Operation(symbol: char, threshold: int)

predicate ValidInput(n: int, q: int, arr: seq<int>, operations: seq<Operation>)
{
  n >= 1 && n <= 100000 &&
  |arr| == n &&
  |operations| == q &&
  (forall i :: 0 <= i < |arr| ==> -100000 <= arr[i] <= 100000) &&
  (forall i :: 0 <= i < |operations| ==> 
    (operations[i].symbol == '>' || operations[i].symbol == '<') &&
    -100000 <= operations[i].threshold <= 100000)
}

function ApplyOperation(arr: seq<int>, op: Operation): seq<int>
{
  match op {
    case Operation(symbol, threshold) =>
      if symbol == '>' then
        seq(|arr|, i requires 0 <= i < |arr| => 
          if arr[i] > threshold then -arr[i] else arr[i])
      else
        seq(|arr|, i requires 0 <= i < |arr| => 
          if arr[i] < threshold then -arr[i] else arr[i])
  }
}

function ApplyOperationsSequentially(arr: seq<int>, operations: seq<Operation>): seq<int>
  decreases |operations|
{
  if |operations| == 0 then arr
  else 
    var transformedArray := ApplyOperation(arr, operations[0]);
    ApplyOperationsSequentially(transformedArray, operations[1..])
}

predicate ValidOutput(result: seq<int>, n: int)
{
  |result| == n &&
  (forall i :: 0 <= i < |result| ==> -100000 <= result[i] <= 100000)
}

predicate ValidArray(arr: seq<int>)
{
  forall i :: 0 <= i < |arr| ==> -100000 <= arr[i] <= 100000
}
// </vc-preamble>

// <vc-helpers>

lemma ApplyOperationPreservesLength(arr: seq<int>, op: Operation)
  ensures |ApplyOperation(arr, op)| == |arr|
{
}

lemma ApplyOperationPreservesBounds(arr: seq<int>, op: Operation)
  requires ValidArray(arr)
  ensures ValidArray(ApplyOperation(arr, op))
{
  var result := ApplyOperation(arr, op);
  forall i | 0 <= i < |result|
    ensures -100000 <= result[i] <= 100000
  {
    assert 0 <= i < |arr|;
    assert -100000 <= arr[i] <= 100000;
    assert -100000 <= -arr[i] <= 100000;
  }
}

lemma ApplyOperationsSequentiallyPreservesBounds(arr: seq<int>, operations: seq<Operation>)
  requires ValidArray(arr)
  ensures ValidArray(ApplyOperationsSequentially(arr, operations))
  decreases |operations|
{
  if |operations| == 0 {
  } else {
    var transformedArray := ApplyOperation(arr, operations[0]);
    ApplyOperationPreservesBounds(arr, operations[0]);
    ApplyOperationsSequentiallyPreservesBounds(transformedArray, operations[1..]);
  }
}

lemma ApplyOperationsSequentiallyPreservesLength(arr: seq<int>, operations: seq<Operation>)
  ensures |ApplyOperationsSequentially(arr, operations)| == |arr|
  decreases |operations|
{
  if |operations| == 0 {
  } else {
    var transformedArray := ApplyOperation(arr, operations[0]);
    ApplyOperationPreservesLength(arr, operations[0]);
    ApplyOperationsSequentiallyPreservesLength(transformedArray, operations[1..]);
  }
}

lemma SeqSliceProperty(operations: seq<Operation>, i: int)
  requires 0 <= i < |operations|
  ensures operations[..i+1] == operations[..i] + [operations[i]]
{
}

lemma ApplyOperationsSequentiallySliceProperty(arr: seq<int>, operations: seq<Operation>, i: int)
  requires 0 <= i < |operations|
  ensures ApplyOperationsSequentially(arr, operations[..i+1]) == 
          ApplyOperationsSequentially(arr, operations[..i] + [operations[i]])
{
  SeqSliceProperty(operations, i);
}

lemma ApplyOperationsSequentiallyAppendProperty(arr: seq<int>, operations: seq<Operation>, op: Operation)
  ensures ApplyOperationsSequentially(arr, operations + [op]) == 
          ApplyOperation(ApplyOperationsSequentially(arr, operations), op)
  decreases |operations|
{
  if |operations| == 0 {
    assert operations + [op] == [op];
    assert ApplyOperationsSequentially(arr, [op]) == ApplyOperation(arr, op);
    assert ApplyOperationsSequentially(arr, operations) == arr;
  } else {
    assert operations + [op] == [operations[0]] + (operations[1..] + [op]);
    ApplyOperationsSequentiallyAppendProperty(ApplyOperation(arr, operations[0]), operations[1..], op);
  }
}
// </vc-helpers>

// <vc-spec>
method Solve(n: int, q: int, arr: seq<int>, operations: seq<Operation>) returns (result: seq<int>)
  requires ValidInput(n, q, arr, operations)
  requires q >= 0
  ensures ValidOutput(result, n)
  ensures result == ApplyOperationsSequentially(arr, operations)
// </vc-spec>
// <vc-code>
{
  result := arr;

  for i := 0 to q
    invariant 0 <= i <= q
    invariant |result| == n
    invariant ValidArray(result)
    invariant result == ApplyOperationsSequentially(arr, operations[..i])
  {
    ApplyOperationPreservesLength(result, operations[i]);
    ApplyOperationPreservesBounds(result, operations[i]);
    
    ApplyOperationsSequentiallySliceProperty(arr, operations, i);
    ApplyOperationsSequentiallyAppendProperty(arr, operations[..i], operations[i]);
    
    result := ApplyOperation(result, operations[i]);
  }
  
  assert operations[..q] == operations;
}
// </vc-code>
