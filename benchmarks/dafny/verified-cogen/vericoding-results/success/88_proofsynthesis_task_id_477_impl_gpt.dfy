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
/* helper modified by LLM (iteration 2): proves shifting uppercase letters by 32 stays within char bounds */
lemma UpperCaseShiftWithinRange(c: char)
  requires IsUpperCase(c)
  ensures c as int + 32 < 65536
{
}
// </vc-helpers>

// <vc-spec>
method ToLowercase(str1: array<char>) returns (result: array<char>)
    ensures result.Length == str1.Length
    ensures forall i :: 0 <= i < str1.Length ==> 
        result[i] == (if IsUpperCase(str1[i]) then Shift32Spec(str1[i]) else str1[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement lowercase conversion and remove redundant null invariant */
  var n := str1.Length;
  result := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == (if IsUpperCase(str1[j]) then Shift32Spec(str1[j]) else str1[j])
    decreases n - i
  {
    var ch := str1[i];
    if IsUpperCase(ch) {
      UpperCaseShiftWithinRange(ch);
      result[i] := Shift32Spec(ch);
    } else {
      result[i] := ch;
    }
    i := i + 1;
  }
}
// </vc-code>
