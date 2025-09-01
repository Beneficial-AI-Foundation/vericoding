function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>

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
  var i := 0;
  var acc := psum(ops[..0]);
  var ok := true;
  ghost var witnessValid := false;
  ghost var w := 0;

  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant acc == psum(ops[..i])
    invariant ok ==> (forall j:int :: 0 <= j <= i ==> psum(ops[..j]) >= 0)
    invariant witnessValid ==> 0 <= w <= i && psum(ops[..w]) < 0
    invariant !ok ==> witnessValid
    decreases |ops| - i
  {
    var nextAcc := psum(ops[..i+1]);

    if ok {
      if nextAcc < 0 {
        ok := false;
        witnessValid := true;
        w := i + 1;
      } else {
        // ok remains true and nextAcc >= 0
      }
    }

    acc := nextAcc;
    i := i + 1;
  }

  res := ok;

  if !res {
    assert witnessValid;
    assert 0 <= w <= |ops| && psum(ops[..w]) < 0;
    assert exists j:int :: 0 <= j <= |ops| && psum(ops[..j]) < 0;
  } else {
    assert forall j:int :: 0 <= j <= |ops| ==> psum(ops[..j]) >= 0;
  }
}
// </vc-code>

