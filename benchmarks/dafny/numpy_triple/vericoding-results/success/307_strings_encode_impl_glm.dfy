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
/* helper modified by LLM (iteration 4): fixed EncodeChar to handle all characters properly */
function EncodeChar(c: char): seq<int>
{
    if IsASCII(c) then [c as int] else [0xC0, (c as int) % 64 + 128]
}

/* helper modified by LLM (iteration 4): fixed EncodeString to handle empty strings properly */
function EncodeString(s: string): seq<int>
    decreases |s|
{
    if |s| == 0 then []
    else if |s| == 1 then EncodeChar(s[0])
    else EncodeChar(s[0]) + EncodeString(s[1..])
}

/* helper modified by LLM (iteration 4): updated lemma for fixed EncodeChar */
lemma EncodeCharValid(c: char)
    ensures IsValidByteArray(EncodeChar(c))
{
    if IsASCII(c) {
        assert EncodeChar(c) == [c as int];
    } else {
        assert EncodeChar(c) == [0xC0, (c as int) % 64 + 128];
    }
}

/* helper modified by LLM (iteration 4): updated lemma for fixed EncodeString */
lemma EncodeStringValid(s: string)
    ensures IsValidByteArray(EncodeString(s))
{
    if s == "" {
        assert EncodeString(s) == [];
    } else if |s| == 1 {
        EncodeCharValid(s[0]);
    } else {
        EncodeStringValid(s[1..]);
        EncodeCharValid(s[0]);
        var A := EncodeChar(s[0]);
        var B := EncodeString(s[1..]);
        assert EncodeString(s) == A + B;
        forall i | 0 <= i < |A| + |B|
            ensures 0 <= (A+B)[i] <= 255
        {
            if i < |A| {
                assert (A+B)[i] == A[i];
            } else {
                var j := i - |A|;
                assert (A+B)[i] == B[j];
            }
        }
    }
}

/* helper modified by LLM (iteration 4): updated lemma for fixed length properties */
lemma EncodeStringLengthProperties(s: string)
    ensures if IsASCIIString(s) then |EncodeString(s)| == |s| else |EncodeString(s)| >= |s|
{
    if s == "" {
        // Then |s| == 0, and |EncodeString(s)| == 0.
    } else if |s| == 1 {
        var encLen := |EncodeChar(s[0])|;
        if IsASCIIString(s) {
            assert encLen == 1;
            assert |EncodeString(s)| == 1 == |s|;
        } else {
            assert encLen == 2;
            assert |EncodeString(s)| == 2 >= 1 == |s|;
        }
    } else {
        EncodeStringLengthProperties(s[1..]);
        var encLen := |EncodeChar(s[0])|;
        var restLen := |EncodeString(s[1..])|;
        var totalLen := encLen + restLen;
        
        if IsASCIIString(s) {
            assert encLen == 1;
            assert restLen == |s[1..]|;
            assert totalLen == 1 + (|s| - 1) == |s|;
        } else {
            assert encLen >= 1;
            assert restLen >= |s[1..]|;
            assert totalLen >= |s|;
        }
    }
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
/* code modified by LLM (iteration 5): replaced sequence comprehension with loop to fix index out of range error */
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == EncodeString(a[j])
  {
    result := result + [EncodeString(a[i])];
    i := i + 1;
  }

  // Prove that every byte array is valid
  forall i | 0 <= i < |a| 
    ensures IsValidByteArray(result[i])
  {
    EncodeStringValid(a[i]);
  }

  // Prove the UTF-8 specific properties when encoding is "utf-8"
  if encoding == "utf-8" {
    // For ASCII strings, the length must be equal to the string length
    forall i | 0 <= i < |a| && IsASCIIString(a[i])
      ensures |result[i]| == |a[i]|
    {
      EncodeStringLengthProperties(a[i]);
    }

    // For any string, the encoded length must be at least the string length
    forall i | 0 <= i < |a|
      ensures |result[i]| >= |a[i]|
    {
      EncodeStringLengthProperties(a[i]);
    }
  }
}
// </vc-code>
