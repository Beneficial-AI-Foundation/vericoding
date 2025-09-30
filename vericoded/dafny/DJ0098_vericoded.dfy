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

// </vc-helpers>

// <vc-spec>
method ToLowercase(str1: array<char>) returns (result: array<char>)
    ensures result.Length == str1.Length
    ensures forall i :: 0 <= i < str1.Length ==> 
        result[i] == (if IsUpperCase(str1[i]) then Shift32Spec(str1[i]) else str1[i])
// </vc-spec>
// <vc-code>
{
  result := new char[str1.Length];
  var i := 0;
  while i < str1.Length
    invariant 0 <= i <= str1.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (if IsUpperCase(str1[j]) then Shift32Spec(str1[j]) else str1[j])
  {
    if IsUpperCase(str1[i]) {
      result[i] := Shift32Spec(str1[i]);
    } else {
      result[i] := str1[i];
    }
    i := i + 1;
  }
}
// </vc-code>
