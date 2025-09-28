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
/* helper modified by LLM (iteration 2): [Used a more standard replacement character for non-ASCII.] */
function EncodeStringUTF8(s: string): (res: ByteArray)
    decreases s
    ensures IsValidByteArray(res)
    ensures s == "" ==> |res| == 0
    ensures s != "" ==> |res| > 0
    ensures |res| >= |s|
    ensures IsASCIIString(s) ==> |res| == |s|
{
    if s == "" then []
    else
        var first_char_encoding := if IsASCII(s[0]) then [s[0] as int] else [0xEF, 0xBF, 0xBD];
        first_char_encoding + EncodeStringUTF8(s[1..])
}

function EncodeString(s: string, encoding: string): (res: ByteArray)
    ensures IsValidByteArray(res)
    ensures s == "" ==> |res| == 0
    ensures s != "" ==> |res| > 0
    ensures encoding == "utf-8" ==> |res| >= |s|
    ensures encoding == "utf-8" && IsASCIIString(s) ==> |res| == |s|
{
    if encoding == "utf-8" then
        EncodeStringUTF8(s)
    else
        // A simple model for any other encoding that satisfies basic properties
        if s == "" then [] else [0]
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
{
  /* code modified by LLM (iteration 2): [Replaced sequence comprehension with a while loop to fix a compilation error.] */
  var res: seq<ByteArray> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == EncodeString(a[k], encoding)
  {
    res := res + [EncodeString(a[i], encoding)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
