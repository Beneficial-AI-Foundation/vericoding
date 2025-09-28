// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ModCongruence(a: int, b: int, n: int)
  requires n > 0
  requires a % n == b % n
  ensures (a - b) % n == 0
{
  var ra := a % n;
  var qa := a / n;
  assert a == qa * n + ra;
  
  var rb := b % n;
  var qb := b / n;
  assert b == qb * n + rb;
  
  assert a - b == (qa - qb) * n + (ra - rb);
  assert ra == rb;
  assert a - b == (qa - qb) * n;
  assert (a - b) % n == 0;
}

/* helper modified by LLM (iteration 2): fixed compilation errors by changing iset to set for finite set reasoning */
lemma ModShiftIsBijection(n: nat, c: int)
    requires n > 0
    ensures (set i | 0 <= i < n :: (i+c)%n) == (set j | 0 <= j < n :: j)
{
    var S := set i | 0 <= i < n :: i;
    var f := (i:int) => (i+c)%n;
    var image_S := set i | i in S :: f(i);

    forall y | y in image_S ensures y in S {
        var x :| x in S && y == f(x);
        assert 0 <= y < n;
    }

    forall i, j | i in S && j in S && f(i) == f(j)
        ensures i == j
    {
        ModCongruence(i+c, j+c, n);
        assert (i - j) % n == 0;
        assert -n < i-j < n;
        assert i-j == 0;
    }

    assert |image_S| == |S|;
    assert image_S == S;
}
// </vc-helpers>

// <vc-spec>
method FFTShift(x: seq<real>) returns (result: seq<real>)
  requires |x| >= 0
  ensures |result| == |x|
  // Main transformation: each element at position i comes from position (i + |x| - |x|/2) % |x|
  ensures |x| > 0 ==> forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| - |x|/2) % |x|]
  // Bijective property: every input element appears exactly once in output
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j]
  // Inverse bijective property: every output element comes from exactly one input element  
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j]
  // Multiset equality: same elements with same multiplicities
  ensures multiset(result) == multiset(x)
  // Handle empty sequence case
  ensures |x| == 0 ==> result == []
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): initial implementation of fftshift logic */
  var n := |x|;
  if n == 0 {
    result := [];
  } else {
    var shift := n - n/2;
    ModShiftIsBijection(n, shift);
    result := seq(n, i => x[(i + shift) % n]);
  }
}
// </vc-code>
