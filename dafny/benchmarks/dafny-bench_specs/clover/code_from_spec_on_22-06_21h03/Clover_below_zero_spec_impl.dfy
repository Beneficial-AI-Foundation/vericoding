//IMPL 
method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{
  s := new int[|operations| + 1];
  s[0] := 0;
  result := false;
  
  var i := 0;
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant s.Length == |operations| + 1
    invariant s[0] == 0
    invariant forall j :: 0 <= j < i ==> s[j+1] == s[j] + operations[j]
    /* code modified by LLM (iteration 4): Fixed invariants to properly handle result logic */
    invariant result == true <==> (exists j :: 1 <= j <= i && s[j] < 0)
    invariant result == false ==> forall j :: 0 <= j <= i ==> s[j] >= 0
  {
    s[i+1] := s[i] + operations[i];
    /* code modified by LLM (iteration 4): Update result if we find a negative value */
    if s[i+1] < 0 {
      result := true;
    }
    i := i + 1;
  }
}