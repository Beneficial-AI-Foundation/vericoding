// <vc-preamble>
predicate IsUpperCase(c: char)
{
    c >= 'A' && c <= 'Z'
}

function Shift32Spec(c: char): char
    requires IsUpperCase(c)
    requires c as int + 32 < 65536
{
    if c as int + 32 < 65536 then (c as int + 32) as char else c
}
// </vc-preamble>

// <vc-helpers>
lemma UpperBound(c: char)
  requires IsUpperCase(c)
  ensures c as int + 32 < 65536
{ }

// </vc-helpers>

// <vc-spec>
method ToLowercase(str1: array<char>) returns (result: array<char>)
    ensures result.Length == str1.Length
    ensures forall i :: 0 <= i < str1.Length ==> 
        result[i] == (if IsUpperCase(str1[i]) then Shift32Spec(str1[i]) else str1[i])
// </vc-spec>
// <vc-code>
{
  var res := new char[str1.Length];
  var i := 0;
  result := res;
  while i < str1.Length
    invariant 0 <= i <= str1.Length
    invariant result.Length == str1.Length
    invariant forall k :: 0 <= k < i ==> result[k] == (if IsUpperCase(str1[k]) then Shift32Spec(str1[k]) else str1[k])
  {
    var c := str1[i];
    if IsUpperCase(c) {
      UpperBound(c);
      result[i] := Shift32Spec(c);
    } else {
      result[i] := c;
    }
    i := i + 1;
  }
}
// </vc-code>
