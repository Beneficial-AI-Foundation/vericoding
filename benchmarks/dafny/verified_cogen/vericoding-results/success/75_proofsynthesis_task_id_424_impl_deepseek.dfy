// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function GetLastChar(arr: array<char>): char requires arr.Length > 0 reads arr { arr[arr.Length - 1] }
// </vc-helpers>

// <vc-spec>
method ExtractRearChars(s: array<array<char>>) returns (result: array<char>)
    requires forall i :: 0 <= i < s.Length ==> s[i].Length > 0
    ensures s.Length == result.Length
    ensures forall i :: 0 <= i < s.Length ==> result[i] == s[i][s[i].Length - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added reads clause and fixed loop invariant */
  result := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == GetLastChar(s[j])
  {
    result[i] := GetLastChar(s[i]);
    i := i + 1;
  }
}
// </vc-code>
