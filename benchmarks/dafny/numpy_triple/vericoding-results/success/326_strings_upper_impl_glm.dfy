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
lemma CharToUpperIdempotent(c: char)
  ensures CharToUpper(CharToUpper(c)) == CharToUpper(c)
{
  if 'a' <= c <= 'z' {
    assert CharToUpper(c) == (c as int - 'a' as int + 'A' as int) as char;
    assert 'A' <= CharToUpper(c) <= 'Z';
  } else {
    // CharToUpper(c) = c, so CharToUpper(CharToUpper(c)) = c = CharToUpper(c)
  }
}

lemma StringToUpperIdempotent(s: string)
  decreases |s|
  ensures StringToUpper(StringToUpper(s)) == StringToUpper(s)
{
  if |s| == 0 {
  } else {
    calc {
      StringToUpper(StringToUpper(s));
      StringToUpper([CharToUpper(s[0])] + StringToUpper(s[1..]));
      [CharToUpper(CharToUpper(s[0]))] + StringToUpper(StringToUpper(s[1..]));
      { CharToUpperIdempotent(s[0]); }
      [CharToUpper(s[0])] + StringToUpper(StringToUpper(s[1..]));
      { StringToUpperIdempotent(s[1..]); }
      [CharToUpper(s[0])] + StringToUpper(s[1..]);
      StringToUpper(s);
    }
  }
}
/* helper modified by LLM (iteration 2): added lemma to prove idempotent property for sequence of strings */
lemma UpperIdempotent(a: seq<string>)
  ensures forall i :: 0 <= i < |a| ==> StringToUpper(StringToUpper(a[i])) == StringToUpper(a[i])
{
  if |a| == 0 {
  } else {
    forall i | 0 <= i < |a| {
      StringToUpperIdempotent(a[i]);
    }
  }
}
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
  /* code modified by LLM (iteration 2): removed ghost block and added lemma call for idempotent proof */
  result := seq(|a|, i requires 0 <= i < |a| => StringToUpper(a[i]));
  UpperIdempotent(a);
}
// </vc-code>
