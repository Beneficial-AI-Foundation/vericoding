// <vc-preamble>
// Data type character codes used in NumPy ufunc type signatures
datatype TypeCode = 
  | Bool       // '?'
  | Byte       // 'b'
  | UByte      // 'B'
  | Short      // 'h'
  | UShort     // 'H'
  | Int        // 'i'
  | UInt       // 'I'
  | Long       // 'l'
  | ULong      // 'L'
  | LongLong   // 'q'
  | ULongLong  // 'Q'
  | Float32    // 'f'
  | Float64    // 'd'
  | LongDouble // 'g'
  | Complex64  // 'F'
  | Complex128 // 'D'
  | CLongDouble // 'G'
  | Object     // 'O'

// Type signature representing input->output mapping for ufuncs
datatype TypeSignature = TypeSignature(
  input_types: seq<TypeCode>,
  output_type: TypeCode
)

// Convert TypeCode to character representation
function typeCodeToChar(tc: TypeCode): char
{
  match tc
  case Bool => '?'
  case Byte => 'b'
  case UByte => 'B'
  case Short => 'h'
  case UShort => 'H'
  case Int => 'i'
  case UInt => 'I'
  case Long => 'l'
  case ULong => 'L'
  case LongLong => 'q'
  case ULongLong => 'Q'
  case Float32 => 'f'
  case Float64 => 'd'
  case LongDouble => 'g'
  case Complex64 => 'F'
  case Complex128 => 'D'
  case CLongDouble => 'G'
  case Object => 'O'
}

// Convert sequence of TypeCode to string of characters
function typeSequenceToString(types: seq<TypeCode>): string
{
  seq(|types|, i requires 0 <= i < |types| => typeCodeToChar(types[i]))
}

// Format a type signature as a string (input1input2...->output)
function formatTypeSignature(sig: TypeSignature): string
{
  var input_str := typeSequenceToString(sig.input_types);
  input_str + "->" + [typeCodeToChar(sig.output_type)]
}

// Returns the list of supported data type signatures for a universal function
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method types(ufunc_signatures: seq<TypeSignature>) returns (result: seq<string>)
  requires forall i :: 0 <= i < |ufunc_signatures| ==> |ufunc_signatures[i].input_types| > 0
  ensures |result| == |ufunc_signatures|
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == formatTypeSignature(ufunc_signatures[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |ufunc_signatures|
    invariant 0 <= i <= |ufunc_signatures|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == formatTypeSignature(ufunc_signatures[j])
  {
    result := result + [formatTypeSignature(ufunc_signatures[i])];
    i := i + 1;
  }
}
// </vc-code>
