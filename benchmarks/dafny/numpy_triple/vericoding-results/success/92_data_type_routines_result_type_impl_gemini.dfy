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
/* helper modified by LLM (iteration 4): [fixed syntax: changed 'function method' to 'function' and fixed 'if' expression syntax] */
function FindMaxRankIndex(operands: seq<NumpyOperand>): (index: nat)
    requires |operands| > 0
    ensures 0 <= index < |operands|
    ensures TypeRank(OperandType(operands[index])) == MaxRank(operands)
{
    if |operands| == 1 then 0
    else
        var tail_index := FindMaxRankIndex(operands[1..]);
        var headRank := TypeRank(OperandType(operands[0]));
        var tailMaxRank := MaxRank(operands[1..]);
        if headRank >= tailMaxRank then 0 else tail_index + 1
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
    /* code modified by LLM (iteration 4): [added invariant to help verification] */
    var maxRank := MaxRank(operands);
    
    var final_idx: nat;

    // Pass 1: Find an array with the max rank.
    var i: nat := 0;
    var found_array: bool := false;
    while i < |operands|
        invariant 0 <= i <= |operands|
        invariant !found_array ==> forall k :: 0 <= k < i ==> !(IsArray(operands[k]) && TypeRank(OperandType(operands[k])) == maxRank)
        invariant found_array ==> 0 <= final_idx < |operands| && IsArray(operands[final_idx]) && TypeRank(OperandType(operands[final_idx])) == maxRank
    {
        if TypeRank(OperandType(operands[i])) == maxRank && IsArray(operands[i]) {
            final_idx := i;
            found_array := true;
            break;
        }
        i := i + 1;
    }

    if !found_array {
        // Pass 2: No array with max rank found, find any operand with max rank.
        final_idx := FindMaxRankIndex(operands);
    }
    
    result := OperandType(operands[final_idx]);
}
// </vc-code>
