// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function EncryptOneChar(c: char): char
{
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
  /* code modified by LLM (iteration 2): [Fixed array-to-string conversion syntax] */
  var res_chars := new char[|s|];
  var i: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> res_chars[k] == EncryptOneChar(s[k])
  {
    res_chars[i] := EncryptOneChar(s[i]);
    i := i + 1;
  }
  result := res_chars[..];
}
// </vc-code>
