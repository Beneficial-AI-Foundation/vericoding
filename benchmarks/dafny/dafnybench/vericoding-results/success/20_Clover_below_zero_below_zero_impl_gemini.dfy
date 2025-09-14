// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  s := new int[|operations| + 1];
  s[0] := 0;
  result := false;
  var i := 0;
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant s.Length == |operations| + 1
    invariant s[0] == 0
    invariant forall k :: 0 <= k < i ==> s[k+1] == s[k] + operations[k]
    invariant result ==> (exists k :: 1 <= k <= i && s[k] < 0)
    invariant !result ==> forall k :: 0 <= k <= i ==> s[k] >= 0
  {
    s[i+1] := s[i] + operations[i];
    if s[i+1] < 0 {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
