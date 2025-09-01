function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psum_prefix(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures psum(s[..i]) == if i == 0 then 0 else psum(s[..i-1]) + s[i-1]
{
  if i > 0 {
    calc {
      psum(s[..i]);
      == { assert s[..i] == s[..i-1] + [s[i-1]]; }
      psum(s[..i-1] + [s[i-1]]);
      == // Definition of psum
      (if |s[..i-1] + [s[i-1]]| == 0 then 0 
       else psum((s[..i-1] + [s[i-1]])[..|s[..i-1] + [s[i-1]]|-1]) + (s[..i-1] + [s[i-1]])[|s[..i-1] + [s[i-1]]| - 1]);
      == { assert |s[..i-1] + [s[i-1]]| == i; }
      psum((s[..i-1] + [s[i-1]])[..i-1]) + (s[..i-1] + [s[i-1]])[i-1];
      == { 
        assert (s[..i-1] + [s[i-1]])[..i-1] == s[..i-1];
        assert (s[..i-1] + [s[i-1]])[i-1] == s[i-1];
      }
      psum(s[..i-1]) + s[i-1];
    }
  }
}

lemma psum_extends(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures psum(s[..i+1]) == psum(s[..i]) + s[i]
{
  psum_prefix(s, i+1);
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var running_sum := 0;
  var i := 0;
  
  while i <= |ops|
    invariant 0 <= i <= |ops|
    invariant running_sum == psum(ops[..i])
    invariant forall j : int :: 0 <= j <= i ==> psum(ops[..j]) >= 0
  {
    if i == |ops| {
      break;
    }
    psum_extends(ops, i);
    assert psum(ops[..i+1]) == running_sum + ops[i];
    running_sum := running_sum + ops[i];
    if running_sum < 0 {
      assert psum(ops[..i+1]) < 0;
      assert 0 <= i+1 <= |ops|;
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>

