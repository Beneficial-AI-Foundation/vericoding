// <vc-preamble>
// Define NumPy data types for type promotion
datatype NumpyDType = 
  | Bool
  | Int8
  | Int16
  | Int32
  | Int64
  | Float32
  | Float64
  | Complex64
  | Complex128

// Define type promotion hierarchy (higher number = higher precedence)
function TypeRank(dtype: NumpyDType): nat
{
  match dtype
    case Bool => 0
    case Int8 => 1
    case Int16 => 2
    case Int32 => 3
    case Int64 => 4
    case Float32 => 5
    case Float64 => 6
    case Complex64 => 7
    case Complex128 => 8
}

// Define operand types (either scalar or array)
datatype NumpyOperand =
  | Scalar(dtype: NumpyDType)
  | Array(dtype: NumpyDType, values: seq<int>)

// Extract the data type from an operand
function OperandType(operand: NumpyOperand): NumpyDType
{
  match operand
    case Scalar(dtype) => dtype
    case Array(dtype, _) => dtype
}

// Check if an operand is an array
predicate IsArray(operand: NumpyOperand)
{
  match operand
    case Scalar(_) => false
    case Array(_, _) => true
}

// Helper function to get maximum rank from a list of operands
function MaxRank(operands: seq<NumpyOperand>): nat
  requires |operands| > 0
{
  if |operands| == 1 then
    TypeRank(OperandType(operands[0]))
  else
    var headRank := TypeRank(OperandType(operands[0]));
    var tailMax := MaxRank(operands[1..]);
    if headRank >= tailMax then headRank else tailMax
}

// Helper predicate to check if a type exists in operands list
predicate TypeExistsInOperands(operands: seq<NumpyOperand>, dtype: NumpyDType)
{
  exists i :: 0 <= i < |operands| && OperandType(operands[i]) == dtype
}

// Helper predicate to check if an array type exists for a given dtype
predicate ArrayTypeExists(operands: seq<NumpyOperand>, dtype: NumpyDType)
{
  exists i :: 0 <= i < |operands| && OperandType(operands[i]) == dtype && IsArray(operands[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed lemma to prove existence of index with maximum rank */
lemma MaxRankIsAchieved(operands: seq<NumpyOperand>)
  requires |operands| > 0
  ensures exists i :: 0<=i<|operands| && TypeRank(OperandType(operands[i])) == MaxRank(operands)
  decreases |operands|
{
  if |operands| == 1 {
    // Base case: only one element, so index 0 is the one.
    assert 0 <= 0 < 1;
    assert TypeRank(OperandType(operands[0])) == MaxRank(operands);
  } else {
    MaxRankIsAchieved(operands[1..]); // Recursive call on tail
    var headRank := TypeRank(OperandType(operands[0]));
    var tailMax := MaxRank(operands[1..]);
    if headRank >= tailMax {
      // Then the maximum is headRank, achieved at index 0.
      assert 0 <= 0 < |operands|;
      assert TypeRank(OperandType(operands[0])) == headRank;
      assert headRank == MaxRank(operands);
    } else {
      // Then the maximum is tailMax, which is achieved in the tail.
      // We know by the lemma that there exists j in [0, |operands[1..]|) such that:
      ghost var j : int;
      j :| 0 <= j < |operands[1..]| && TypeRank(OperandType(operands[1..][j])) == tailMax;
      // Now, let i = j + 1, which is in [1, |operands|) because j in [0, |operands|-1)
      var i := j + 1;
      assert 0 <= i < |operands|;
      assert TypeRank(OperandType(operands[i])) == tailMax;
      assert tailMax == MaxRank(operands);
      assert TypeRank(OperandType(operands[i])) == MaxRank(operands);
      // Now we have an index i that satisfies the condition.
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ResultType(operands: seq<NumpyOperand>) returns (result: NumpyDType)
  requires |operands| > 0
  ensures TypeRank(result) == MaxRank(operands)
  ensures (exists i :: 0 <= i < |operands| && TypeRank(OperandType(operands[i])) == MaxRank(operands) && IsArray(operands[i])) ==>
    (exists i :: 0 <= i < |operands| && OperandType(operands[i]) == result && IsArray(operands[i]))
  ensures !(exists i :: 0 <= i < |operands| && TypeRank(OperandType(operands[i])) == MaxRank(operands) && IsArray(operands[i])) ==>
    (exists i :: 0 <= i < |operands| && OperandType(operands[i]) == result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed variable declaration using assign-such-that */
  var maxRank := MaxRank(operands);
  MaxRankIsAchieved(operands);
  var i : int;
  i :| 0 <= i < |operands| && TypeRank(OperandType(operands[i])) == maxRank;
  result := OperandType(operands[i]);
}
// </vc-code>
