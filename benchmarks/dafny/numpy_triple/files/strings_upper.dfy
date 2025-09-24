// <vc-preamble>
// Helper function to convert a character to uppercase
function CharToUpper(c: char): char
{
  if 'a' <= c <= 'z' then (c as int - 'a' as int + 'A' as int) as char else c
}

// Helper function to check if a character is alphabetic
function IsAlpha(c: char): bool
{
  ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

// Helper function to check if a character is lowercase
function IsLower(c: char): bool
{
  'a' <= c <= 'z'
}

// Helper function to convert an entire string to uppercase
function StringToUpper(s: string): string
  ensures |StringToUpper(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> StringToUpper(s)[i] == CharToUpper(s[i])
{
  if |s| == 0 then ""
  else [CharToUpper(s[0])] + StringToUpper(s[1..])
}

/**
 * Convert each string in the input sequence to uppercase.
 * This method applies uppercase transformation element-wise while preserving
 * the sequence structure and individual string lengths.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Upper(a: seq<string>) returns (result: seq<string>)
  // No preconditions needed - works for any sequence of strings
  
  // Postconditions capturing all mathematical properties
  ensures |result| == |a|  // Vector length preservation
  
  // Element-wise correctness and properties for each string
  ensures forall i :: 0 <= i < |a| ==>
    // Fundamental correctness: result matches string-to-upper transformation
    result[i] == StringToUpper(a[i]) &&
    
    // Length preservation: each result string has same length as original
    |result[i]| == |a[i]| &&
    
    // Empty string handling: empty input produces empty output
    (|a[i]| == 0 ==> result[i] == "") &&
    
    // Character-level transformation correctness
    (forall j :: 0 <= j < |a[i]| ==> result[i][j] == CharToUpper(a[i][j])) &&
    
    // Idempotent property: applying upper twice gives same result as once
    StringToUpper(result[i]) == result[i] &&
    
    // Case preservation: non-alphabetic characters remain unchanged
    (forall j :: 0 <= j < |a[i]| ==> !IsAlpha(a[i][j]) ==> result[i][j] == a[i][j]) &&
    
    // Alphabetic transformation: lowercase letters become uppercase
    (forall j :: 0 <= j < |a[i]| ==> IsLower(a[i][j]) ==> result[i][j] == CharToUpper(a[i][j]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
