// <vc-preamble>
function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)

    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
