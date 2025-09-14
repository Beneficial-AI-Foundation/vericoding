// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  result := 0;
  var bb := b;
  var addend := a;
  if (bb < 0) {
    addend := -addend;
    bb := -bb;
  }
  var i := bb;
  while i > 0
    invariant result == (bb - i) * addend
    invariant i >= 0
    decreases i
  {
    result := result + addend;
    i := i - 1;
  }
}
// </vc-code>
