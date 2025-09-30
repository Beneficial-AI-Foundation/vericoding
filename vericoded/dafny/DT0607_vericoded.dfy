// <vc-preamble>
// Type alias for ByteArray to match original semantics
type ByteArray = seq<int>

// Predicate to check if a character is ASCII (0-127)
predicate IsASCII(c: char)
{
    0 <= c as int <= 127
}

// Predicate to check if a string contains only ASCII characters
predicate IsASCIIString(s: string)
{
    forall i :: 0 <= i < |s| ==> IsASCII(s[i])
}

// Predicate to check if a byte array represents valid byte values (0-255)
predicate IsValidByteArray(bytes: seq<int>)
{
    forall i :: 0 <= i < |bytes| ==> 0 <= bytes[i] <= 255
}

// Method to encode strings using the specified codec
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma for deterministic encoding property */
function EncodeString(s: string, encoding: string, errors: string): ByteArray
{
  if s == "" then
    []
  else if encoding == "utf-8" then
    EncodeUTF8(s)
  else
    EncodeUTF8(s)  // Default to UTF-8 for any unrecognized encoding
}

function EncodeUTF8(s: string): ByteArray
{
  if |s| == 0 then
    []
  else
    EncodeUTF8Char(s[0]) + EncodeUTF8(s[1..])
}

function EncodeUTF8Char(c: char): ByteArray
{
  var codePoint := c as int;
  if codePoint <= 0x7F then
    [codePoint]
  else if codePoint <= 0x7FF then
    [0xC0 + (codePoint / 64), 0x80 + (codePoint % 64)]
  else if codePoint <= 0xFFFF then
    [0xE0 + (codePoint / 4096), 0x80 + ((codePoint / 64) % 64), 0x80 + (codePoint % 64)]
  else
    [0xF0 + (codePoint / 262144), 0x80 + ((codePoint / 4096) % 64), 0x80 + ((codePoint / 64) % 64), 0x80 + (codePoint % 64)]
}

lemma EncodeUTF8CharValid(c: char)
  ensures IsValidByteArray(EncodeUTF8Char(c))
{
}

lemma EncodeUTF8Valid(s: string)
  ensures IsValidByteArray(EncodeUTF8(s))
{
  if |s| > 0 {
    EncodeUTF8CharValid(s[0]);
    EncodeUTF8Valid(s[1..]);
  }
}

lemma EncodeStringValid(s: string, encoding: string, errors: string)
  ensures IsValidByteArray(EncodeString(s, encoding, errors))
{
  if s != "" && encoding == "utf-8" {
    EncodeUTF8Valid(s);
  } else if s != "" {
    EncodeUTF8Valid(s);
  }
}

lemma EncodeUTF8ASCIILength(s: string)
  requires IsASCIIString(s)
  ensures |EncodeUTF8(s)| == |s|
{
  if |s| > 0 {
    assert IsASCII(s[0]);
    assert s[0] as int <= 127;
    assert |EncodeUTF8Char(s[0])| == 1;
    EncodeUTF8ASCIILength(s[1..]);
  }
}

lemma EncodeUTF8MinLength(s: string)
  ensures |EncodeUTF8(s)| >= |s|
{
  if |s| > 0 {
    assert |EncodeUTF8Char(s[0])| >= 1;
    EncodeUTF8MinLength(s[1..]);
  }
}

lemma EncodeStringDeterministic(s1: string, s2: string, encoding: string, errors: string)
  requires s1 == s2
  ensures EncodeString(s1, encoding, errors) == EncodeString(s2, encoding, errors)
{
  // Functions are deterministic by definition in Dafny
}
// </vc-helpers>

// <vc-spec>
method encode(a: seq<string>, encoding: string := "utf-8", errors: string := "strict") 
    returns (result: seq<ByteArray>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> IsValidByteArray(result[i])
    // Deterministic encoding: same input produces same output
    ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] == a[j] ==> result[i] == result[j]
    // Empty strings encode to empty byte arrays
    ensures forall i :: 0 <= i < |a| && a[i] == "" ==> |result[i]| == 0
    // Non-empty strings produce non-empty byte arrays
    ensures forall i :: 0 <= i < |a| && a[i] != "" ==> |result[i]| > 0
    // For UTF-8 encoding, ASCII strings have predictable byte length
    ensures encoding == "utf-8" ==> 
        (forall i :: 0 <= i < |a| && IsASCIIString(a[i]) ==> |result[i]| == |a[i]|)
    // For UTF-8 encoding, encoded size is at least the string length
    ensures encoding == "utf-8" ==> 
        (forall i :: 0 <= i < |a| ==> |result[i]| >= |a[i]|)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added explicit assertion to help verify deterministic encoding invariant */
{
  result := [];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == EncodeString(a[k], encoding, errors)
    invariant forall k :: 0 <= k < i ==> IsValidByteArray(result[k])
    invariant forall k, j :: 0 <= k < i && 0 <= j < i && a[k] == a[j] ==> result[k] == result[j]
    invariant forall k :: 0 <= k < i && a[k] == "" ==> |result[k]| == 0
    invariant forall k :: 0 <= k < i && a[k] != "" ==> |result[k]| > 0
    invariant encoding == "utf-8" ==> (forall k :: 0 <= k < i && IsASCIIString(a[k]) ==> |result[k]| == |a[k]|)
    invariant encoding == "utf-8" ==> (forall k :: 0 <= k < i ==> |result[k]| >= |a[k]|)
  {
    var encoded := EncodeString(a[i], encoding, errors);
    EncodeStringValid(a[i], encoding, errors);
    
    // Establish deterministic encoding for all previous entries that match current string
    forall j | 0 <= j < i && a[j] == a[i]
      ensures result[j] == encoded
    {
      assert result[j] == EncodeString(a[j], encoding, errors);
      assert a[j] == a[i];
      EncodeStringDeterministic(a[j], a[i], encoding, errors);
      assert EncodeString(a[j], encoding, errors) == EncodeString(a[i], encoding, errors);
      assert result[j] == encoded;
    }
    
    if encoding == "utf-8" {
      if IsASCIIString(a[i]) {
        EncodeUTF8ASCIILength(a[i]);
      }
      EncodeUTF8MinLength(a[i]);
    }
    
    result := result + [encoded];
    i := i + 1;
  }
}
// </vc-code>
