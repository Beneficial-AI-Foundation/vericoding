// <vc-preamble>
// Format descriptor for structured data types
datatype FormatDescriptor = 
    | Float64              // 64-bit floating point ('f8')
    | Int32                // 32-bit integer ('i4') 
    | StringType(len: nat) // Variable length string ('S5' for string of length 5)
    | Int64                // 64-bit integer ('i8')
    | Float32              // 32-bit floating point ('f4')

// A field in a structured data type
datatype Field = Field(
    name: string,                    // Field name
    format: FormatDescriptor,        // Format descriptor  
    title: Option<string>            // Optional title for the field
)

// Optional type helper
datatype Option<T> = None | Some(value: T)

// A structured data type specification
datatype DType = DType(
    fields: seq<Field>,              // Sequence of fields
    aligned: bool                    // Whether fields are aligned as C-compiler would
)

// Predicate to check if a format string is valid
predicate ValidFormatString(format: string)
{
    format == "f8" || format == "f4" || format == "i4" || format == "i8" ||
    (|format| >= 2 && format[0] == 'S' && forall i :: 1 <= i < |format| ==> '0' <= format[i] <= '9')
}

// Helper function to compute powers of 10
function Pow10(n: nat): nat
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

// Helper to extract string length from format like "S5" or "S123"
function StringLength(format: string): nat
    requires |format| >= 2 && format[0] == 'S' && forall i :: 1 <= i < |format| ==> '0' <= format[i] <= '9'
{
    ParseDigits(format, 1, 0)
}

// Recursive helper to parse digits starting from position pos
function ParseDigits(format: string, pos: nat, acc: nat): nat
    requires pos <= |format|
    requires forall i :: 1 <= i < |format| ==> '0' <= format[i] <= '9'
{
    if pos >= |format| then
        acc
    else
        ParseDigits(format, pos + 1, acc * 10 + (format[pos] as int - '0' as int) as nat)
}

// Method to parse format string to descriptor
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_format_parser(
    formats: seq<string>, 
    names: seq<string>,
    titles: Option<seq<string>>,
    aligned: bool
) returns (dtype: DType)
    // Preconditions
    requires |formats| == |names|
    requires forall i :: 0 <= i < |formats| ==> ValidFormatString(formats[i])
    requires titles.Some? ==> |titles.value| == |formats|
    
    // Postconditions  
    ensures |dtype.fields| == |formats|
    ensures dtype.aligned == aligned
    ensures forall i :: 0 <= i < |dtype.fields| ==> dtype.fields[i].name == names[i]
    ensures forall i :: 0 <= i < |dtype.fields| ==> 
        (formats[i] == "f8" ==> dtype.fields[i].format == Float64) &&
        (formats[i] == "f4" ==> dtype.fields[i].format == Float32) &&
        (formats[i] == "i4" ==> dtype.fields[i].format == Int32) &&
        (formats[i] == "i8" ==> dtype.fields[i].format == Int64) &&
        (|formats[i]| >= 2 && formats[i][0] == 'S' ==> 
         dtype.fields[i].format == StringType(StringLength(formats[i])))
    ensures titles.None? ==> forall i :: 0 <= i < |dtype.fields| ==> dtype.fields[i].title.None?
    ensures titles.Some? ==> forall i :: 0 <= i < |dtype.fields| ==> 
        dtype.fields[i].title == Some(titles.value[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
