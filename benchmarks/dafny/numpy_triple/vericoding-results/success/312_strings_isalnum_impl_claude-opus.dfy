// <vc-preamble>
/*
 * Dafny specification for numpy.strings.isalnum functionality.
 * Returns true for each element if all characters in the string are alphanumeric 
 * and there is at least one character, false otherwise.
 */

// Predicate to check if a character is alphanumeric (letter or digit)
predicate IsAlphanumericChar(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

// Predicate to check if all characters in a string are alphanumeric
predicate AllCharsAlphanumeric(s: string)
{
    forall i :: 0 <= i < |s| ==> IsAlphanumericChar(s[i])
}

// Predicate to check if a string is alphanumeric (non-empty and all chars alphanumeric)
predicate IsAlphanumericString(s: string)
{
    |s| > 0 && AllCharsAlphanumeric(s)
}

// Main method specification for element-wise alphanumeric check
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsAlnum(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == IsAlphanumericString(a[i])
    ensures forall i :: 0 <= i < |a| ==> 
        result[i] == (|a[i]| > 0 && AllCharsAlphanumeric(a[i]))
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == IsAlphanumericString(a[j])
    invariant forall j :: 0 <= j < i ==> result[j] == (|a[j]| > 0 && AllCharsAlphanumeric(a[j]))
  {
    var isAlnum := |a[i]| > 0 && AllCharsAlphanumeric(a[i]);
    result := result + [isAlnum];
    i := i + 1;
  }
}
// </vc-code>
