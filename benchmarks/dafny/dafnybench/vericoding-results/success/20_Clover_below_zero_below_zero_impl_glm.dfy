

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
// </vc-spec>
// <vc-code>
{
  var n := |operations|;
  s := new int[n+1];
  s[0] := 0;
  result := false;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant s.Length == n+1
    invariant s[0] == 0
    invariant forall j :: 0 <= j < i ==> s[j+1] == s[j] + operations[j]
    invariant result == (exists k :: 1 <= k <= i && s[k] < 0)
  {
    if i < n {
      s[i+1] := s[i] + operations[i];
      if s[i+1] < 0 {
        result := true;
      }
    }
  }
}
// </vc-code>

