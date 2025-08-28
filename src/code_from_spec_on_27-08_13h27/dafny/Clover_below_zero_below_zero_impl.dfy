// <vc-helpers>
// No additional helpers or proofs needed for this implementation.
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method below_zero_impl(operations: seq<int>) returns (s: array<int>, result: bool)
  ensures s.Length == |operations| + 1
  ensures s[0] == 0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1] == s[i] + operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{
  s := new int[|operations| + 1];
  s[0] := 0;
  var current := 0;
  result := false;
  
  for i := 0 to |operations|
    invariant 0 <= i <= |operations|
    invariant s.Length == |operations| + 1
    invariant s[0] == 0
    invariant forall k :: 0 <= k < i ==> s[k + 1] == s[k] + operations[k]
    invariant result == true ==> (exists k :: 1 <= k <= i && s[k] < 0)
    invariant result == false ==> forall k :: 0 <= k <= i ==> s[k] >= 0
  {
    current := current + operations[i];
    s[i + 1] := current;
    if current < 0 && !result
    {
      result := true;
    }
  }
}
// </vc-code>
