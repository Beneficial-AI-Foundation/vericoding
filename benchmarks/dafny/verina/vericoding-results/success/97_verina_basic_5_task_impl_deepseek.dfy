// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs(x: int): int { if x < 0 then -x else x }
lemma MultiplicationLemma(a: int, b: int)
  ensures a * b == (if b < 0 then -a * abs(b) else a * abs(b))
{
  if b < 0 {
    assert a * b == -a * -b;
    assert abs(b) == -b;
  } else {
    assert abs(b) == b;
  }
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  var pos_b := abs(b);
  result := 0;
  var i := 0;
  
  while i < pos_b
    invariant 0 <= i <= pos_b
    invariant result == a * i
  {
    result := result + a;
    i := i + 1;
  }
  
  MultiplicationLemma(a, b);
  if b < 0 {
    result := -result;
  }
}
// </vc-code>
