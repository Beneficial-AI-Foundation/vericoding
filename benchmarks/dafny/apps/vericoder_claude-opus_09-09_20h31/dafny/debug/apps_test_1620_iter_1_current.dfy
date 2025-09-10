predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
lemma VerifyPattern(s: string)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  requires forall i :: 0 <= i < |s| ==> 
    if i % 4 == 0 || i % 4 == 1 then s[i] == 'a' else s[i] == 'b'
  ensures forall i :: 0 <= i <= |s| - 3 ==> s[i] != s[i+2]
{
  forall i | 0 <= i <= |s| - 3
    ensures s[i] != s[i+2]
  {
    var mod_i := i % 4;
    var mod_i2 := (i + 2) % 4;
    
    if mod_i == 0 || mod_i == 1 {
      assert s[i] == 'a';
      assert mod_i2 == 2 || mod_i2 == 3;
      assert s[i+2] == 'b';
    } else {
      assert mod_i == 2 || mod_i == 3;
      assert s[i] == 'b';
      assert mod_i2 == 0 || mod_i2 == 1;
      assert s[i+2] == 'a';
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var arr := new char[n];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == 'a' || arr[j] == 'b'
    invariant forall j :: 0 <= j < i ==> 
      if j % 4 == 0 || j % 4 == 1 then arr[j] == 'a' else arr[j] == 'b'
  {
    if i % 4 == 0 || i % 4 == 1 {
      arr[i] := 'a';
    } else {
      arr[i] := 'b';
    }
    i := i + 1;
  }
  
  result := arr[..];
  
  assert forall j :: 0 <= j < n ==> result[j] == 'a' || result[j] == 'b';
  assert forall j :: 0 <= j < n ==> 
    if j % 4 == 0 || j % 4 == 1 then result[j] == 'a' else result[j] == 'b';
  
  VerifyPattern(result);
}
// </vc-code>

