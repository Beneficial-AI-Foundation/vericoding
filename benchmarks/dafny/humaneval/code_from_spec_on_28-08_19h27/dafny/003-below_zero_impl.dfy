function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psum_negative_preservation(s: seq<int>, i: int)
  requires 0 <= i < |s|
  requires psum(s[..i+1]) < 0
  ensures exists j :: 0 <= j <= i && psum(s[..j+1]) < 0
{
  if i == 0 {
    assert psum(s[..1]) < 0;
  } else {
    if psum(s[..i]) < 0 {
      psum_negative_preservation(s, i-1);
    }
  }
}

lemma psum_monotonic_check(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures psum(s[..i+1]) == psum(s[..i]) + s[i]
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert psum(s[..1]) == s[0];
    assert psum(s[..0]) == 0;
  } else {
    assert s[..i+1] == s[..i] + [s[i]];
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def below_zero(operations: List[int]) -> bool
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. Your task is to detect if at any point the balance of account fallls below zero, and at that point function should return True. Otherwise it should return False.
*/
// </vc-description>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |operations| && psum(operations[..i+1]) < 0
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var balance := 0;
  
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant balance == psum(operations[..i])
    invariant forall j :: 0 <= j < i ==> psum(operations[..j+1]) >= 0
  {
    psum_monotonic_check(operations, i);
    balance := balance + operations[i];
    
    if balance < 0 {
      assert psum(operations[..i+1]) < 0;
      return true;
    }
    
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < |operations| ==> psum(operations[..j+1]) >= 0;
  return false;
}
// </vc-code>
