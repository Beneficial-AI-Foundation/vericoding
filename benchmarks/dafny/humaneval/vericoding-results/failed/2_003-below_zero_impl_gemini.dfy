// <vc-preamble>
function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added a lemma to prove the recursive property of psum */
lemma PsumSnoc(s: seq<int>, x: int)
  ensures psum(s + [x]) == psum(s) + x
{
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)

    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): changed invariant and used helper lemma PsumSnoc */
  var sum: int := 0;
  var i: int := 0;
  res := true;

  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant sum == psum(ops[..i])
    invariant res ==> forall k :: 0 <= k <= i ==> psum(ops[..k]) >= 0
  {
    var next_sum := sum + ops[i];
    PsumSnoc(ops[..i], ops[i]); // Establishes psum(ops[..i+1]) == psum(ops[..i]) + ops[i]

    if next_sum < 0 {
      res := false;
      return;
    }
    sum := next_sum;
    i := i + 1;
  }
}
// </vc-code>
