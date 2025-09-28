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
/* helper modified by LLM (iteration 3): CharToUpper idempotency */
lemma CharToUpper_idempotent(c: char)
  ensures CharToUpper(CharToUpper(c)) == CharToUpper(c)
{
  if 'a' <= c <= 'z' {
    var u := CharToUpper(c);
    // u is in uppercase range, so not lowercase
    assert !('a' <= u <= 'z');
    assert CharToUpper(u) == u;
  } else {
    // If c is not lowercase then CharToUpper(c) == c by definition
    assert CharToUpper(c) == c;
  }
}

/* helper modified by LLM (iteration 3): non-alpha preserved by CharToUpper */
lemma CharToUpper_nonalpha_preserved(c: char)
  ensures (!IsAlpha(c)) ==> CharToUpper(c) == c
{
  if !IsAlpha(c) {
    // CharToUpper only changes lowercase letters; non-alphabetic remains unchanged
    assert !('a' <= c <= 'z');
    assert CharToUpper(c) == c;
  }
}

/* helper modified by LLM (iteration 3): StringToUpper idempotency */
lemma StringToUpper_idempotent(s: string)
  ensures StringToUpper(StringToUpper(s)) == StringToUpper(s)
{
  if |s| == 0 {
    // empty string case is trivial
  } else {
    // Inductive hypothesis on tail
    StringToUpper_idempotent(s[1..]);
    // Head char idempotency
    CharToUpper_idempotent(s[0]);
    // Unfold definitions to conclude
    assert StringToUpper(StringToUpper(s)) == [CharToUpper(CharToUpper(s[0]))] + StringToUpper(StringToUpper(s[1..]));
    assert StringToUpper(StringToUpper(s)) == [CharToUpper(s[0])] + StringToUpper(s[1..]);
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
  /* code modified by LLM (iteration 3): implement Upper by mapping StringToUpper over the sequence */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == StringToUpper(a[k])
  {
    var su := StringToUpper(a[i]);
    result := result + [su];
    i := i + 1;
  }
}

// </vc-code>
