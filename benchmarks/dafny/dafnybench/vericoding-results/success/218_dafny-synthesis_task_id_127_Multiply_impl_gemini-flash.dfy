

// <vc-helpers>
lemma MultiplyLemma(a: int, b: int)
  ensures a * b == b * a
{}
// </vc-helpers>

// <vc-spec>
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
// </vc-spec>
// <vc-code>
{
  var res := 0; // Renamed variable to 'res' to avoid conflict
  var b_abs := if b < 0 then -b else b;
  var a_abs := if a < 0 then -a else a;

  if a == 0 || b == 0 {
    return 0;
  }

  // Calculate |a| * |b|
  var i := 0;
  while i < b_abs
    invariant i <= b_abs
    invariant res == a_abs * i
  {
    res := res + a_abs;
    i := i + 1;
  }

  // Adjust sign
  if (a < 0 && b < 0) || (a >= 0 && b >= 0) {
    // Signs are the same: result is positive. `res` is already `|a| * |b|`.
    // Which is `a * b` in this case.
    result := res;
  } else {
    // Signs are different: result is negative. `res` is `|a| * |b|`.
    // We need `-(|a| * |b|)`.
    result := -res;
  }

  return result;
}
// </vc-code>

