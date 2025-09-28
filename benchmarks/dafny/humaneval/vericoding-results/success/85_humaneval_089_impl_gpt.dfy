// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function rotate4(c: char): char {
  if 'a' <= c <= 'z' then
    (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char
  else if 'A' <= c <= 'Z' then
    (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char
  else
    c
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
  var i := 0;
  var r: string := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> (
      if 'a' <= s[j] <= 'z' then
        r[j] == (((s[j] as int - 'a' as int + 4) % 26) + 'a' as int) as char
      else if 'A' <= s[j] <= 'Z' then
        r[j] == (((s[j] as int - 'A' as int + 4) % 26) + 'A' as int) as char
      else
        r[j] == s[j]
    )
    decreases |s| - i
  {
    var c := s[i];
    var rc: char;
    if 'a' <= c <= 'z' {
      rc := (((c as int - 'a' as int + 4) % 26) + 'a' as int) as char;
    } else if 'A' <= c <= 'Z' {
      rc := (((c as int - 'A' as int + 4) % 26) + 'A' as int) as char;
    } else {
      rc := c;
    }
    r := r + [rc];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
