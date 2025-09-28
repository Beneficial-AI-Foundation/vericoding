// <vc-preamble>
function pow2(n: nat): nat 
    decreases n
{
    if n == 0 then
        1
    else
        2 * pow2(n - 1)
}
// </vc-preamble>

// <vc-helpers>
lemma MaskNonNeg(n: nat)
    ensures pow2(n) - 1 >= 0
{
    if n == 0 {
        assert pow2(0) - 1 == 0;
    } else {
        MaskNonNeg(n - 1);
        var t := pow2(n - 1);
        assert t - 1 >= 0;
        assert t >= 1;
        assert 2 * t - 1 >= 0;
    }
}

// </vc-helpers>

// <vc-spec>
method invert(bit_width: nat, a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (pow2(bit_width) - 1) - a[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var mask := pow2(bit_width) - 1;
  MaskNonNeg(bit_width);
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == mask - a[j]
  {
    result[i] := mask - a[i];
    i := i + 1;
  }
}
// </vc-code>
