function abs(x: real): real
{
  if x < 0.0 then -x else x
}

// <vc-helpers>
lemma abs_difference_symmetric(a: real, b: real)
    ensures abs(a - b) == abs(b - a)
{
    if a >= b {
        assert a - b >= 0.0;
        assert b - a <= 0.0;
        assert abs(a - b) == a - b;
        assert abs(b - a) == -(b - a) == a - b;
    } else {
        assert a - b < 0.0;
        assert b - a > 0.0;
        assert abs(a - b) == -(a - b) == b - a;
        assert abs(b - a) == b - a;
    }
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
// </vc-spec>
// <vc-code>
{
    if |numbers| <= 1 {
        return false;
    }
    
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall x, y :: 0 <= x < i && 0 <= y < |numbers| && x != y ==> abs(numbers[x] - numbers[y]) >= threshold
    {
        var j := 0;
        while j < |numbers|
            invariant 0 <= j <= |numbers|
            invariant forall y :: 0 <= y < j && i != y ==> abs(numbers[i] - numbers[y]) >= threshold
            invariant forall x, y :: 0 <= x < i && 0 <= y < |numbers| && x != y ==> abs(numbers[x] - numbers[y]) >= threshold
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                return true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>

