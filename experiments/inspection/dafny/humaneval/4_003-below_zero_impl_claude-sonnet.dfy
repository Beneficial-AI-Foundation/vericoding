// <vc-preamble>
function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove negative balance detection and maintain loop invariant */
lemma PsumPrefix(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures psum(s[..i]) == if i == 0 then 0 else psum(s[..i-1]) + s[i-1]
{
  if i == 0 {
    assert s[..0] == [];
  } else {
    assert s[..i] == s[..i-1] + [s[i-1]];
  }
}

lemma PsumRange(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
  ensures psum(s[..i+1]) == psum(s[..i]) + s[i]
{
  assert s[..i+1] == s[..i] + [s[i]];
}

lemma NegativeBalanceImplies(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires psum(s[..i]) < 0
  ensures exists j :: 0 <= j <= |s| && psum(s[..j]) < 0
{
  assert psum(s[..i]) < 0;
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)

    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed invariant by checking balance before loop body */
{
  var balance := 0;
  var i := 0;
  
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant balance == psum(ops[..i])
    invariant forall j :: 0 <= j <= i ==> psum(ops[..j]) >= 0
  {
    balance := balance + ops[i];
    i := i + 1;
    PsumRange(ops, i-1);
    
    if balance < 0 {
      NegativeBalanceImplies(ops, i);
      res := false;
      return;
    }
  }
  
  res := true;
}
// </vc-code>
