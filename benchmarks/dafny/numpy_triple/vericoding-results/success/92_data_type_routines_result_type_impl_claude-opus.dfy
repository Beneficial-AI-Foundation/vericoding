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
function FindTypeWithMaxRank(operands: seq<NumpyOperand>, maxRank: nat): NumpyDType
  requires |operands| > 0
  requires maxRank == MaxRank(operands)
  ensures TypeRank(FindTypeWithMaxRank(operands, maxRank)) == maxRank
  ensures exists i :: 0 <= i < |operands| && OperandType(operands[i]) == FindTypeWithMaxRank(operands, maxRank)
{
  if TypeRank(OperandType(operands[0])) == maxRank then
    OperandType(operands[0])
  else
    FindTypeWithMaxRank(operands[1..], maxRank)
}

function FindArrayTypeWithMaxRank(operands: seq<NumpyOperand>, maxRank: nat): NumpyDType
  requires |operands| > 0
  requires exists i :: 0 <= i < |operands| && TypeRank(OperandType(operands[i])) == maxRank && IsArray(operands[i])
  ensures TypeRank(FindArrayTypeWithMaxRank(operands, maxRank)) == maxRank
  ensures exists i :: 0 <= i < |operands| && OperandType(operands[i]) == FindArrayTypeWithMaxRank(operands, maxRank) && IsArray(operands[i])
{
  if TypeRank(OperandType(operands[0])) == maxRank && IsArray(operands[0]) then
    OperandType(operands[0])
  else
    FindArrayTypeWithMaxRank(operands[1..], maxRank)
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
  var maxRank := MaxRank(operands);
  
  // Check if there's an array with maximum rank
  var hasArrayWithMaxRank := false;
  var i := 0;
  while i < |operands|
    invariant 0 <= i <= |operands|
    invariant hasArrayWithMaxRank <==> exists j :: 0 <= j < i && TypeRank(OperandType(operands[j])) == maxRank && IsArray(operands[j])
  {
    if TypeRank(OperandType(operands[i])) == maxRank && IsArray(operands[i]) {
      hasArrayWithMaxRank := true;
    }
    i := i + 1;
  }
  
  if hasArrayWithMaxRank {
    result := FindArrayTypeWithMaxRank(operands, maxRank);
  } else {
    result := FindTypeWithMaxRank(operands, maxRank);
  }
}
// </vc-code>
