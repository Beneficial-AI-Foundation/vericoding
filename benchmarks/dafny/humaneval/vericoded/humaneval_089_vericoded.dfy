// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  result := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (
      if 'a' <= s[j] <= 'z' then
        result[j] == (((s[j] as int - 'a' as int + 4) % 26) + 'a' as int) as char
      else if 'A' <= s[j] <= 'Z' then
        result[j] == (((s[j] as int - 'A' as int + 4) % 26) + 'A' as int) as char
      else
        result[j] == s[j]
    )
  {
    var c := s[i];
    var newChar: char;
    if 'a' <= c <= 'z' {
      newChar := (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char;
    } else if 'A' <= c <= 'Z' {
      newChar := (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char;
    } else {
      newChar := c;
    }
    result := result + [newChar];
  }
}
// </vc-code>
