// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function shiftLower(c: char): char
  requires 'a' <= c <= 'z'
  ensures shiftLower(c) as int == (((c as int - 'a' as int + 4) % 26) + 'a' as int)
{
  var offset := (c as int - 'a' as int + 4) % 26;
  (offset + 'a' as int) as char
}

function shiftUpper(c: char): char
  requires 'A' <= c <= 'Z'
  ensures shiftUpper(c) as int == (((c as int - 'A' as int + 4) % 26) + 'A' as int)
{
  var offset := (c as int - 'A' as int + 4) % 26;
  (offset + 'A' as int) as char
}
// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (result: string)
    requires |s| >= 0
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> (
        if 'a' <= s[i] <= 'z' then
            result[i] == (((s[i] as int - 'a' as int + 4) % 26) + 'a' as int) as char
        else if 'A' <= s[i] <= 'Z' then
            result[i] == (((s[i] as int - 'A' as int + 4) % 26) + 'A' as int) as char
        else
            result[i] == s[i]
    )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fix function syntax in helpers */
  var chars := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant chars.Length == |s|
    invariant forall j :: 0 <= j < i ==> (
      if 'a' <= s[j] <= 'z' then
        chars[j] == shiftLower(s[j])
      else if 'A' <= s[j] <= 'Z' then
        chars[j] == shiftUpper(s[j])
      else
        chars[j] == s[j]
    )
  {
    var c := s[i];
    if 'a' <= c <= 'z' {
      chars[i] := shiftLower(c);
    } else if 'A' <= c <= 'Z' {
      chars[i] := shiftUpper(c);
    } else {
      chars[i] := c;
    }
    i := i + 1;
  }
  result := chars[..];
}
// </vc-code>
