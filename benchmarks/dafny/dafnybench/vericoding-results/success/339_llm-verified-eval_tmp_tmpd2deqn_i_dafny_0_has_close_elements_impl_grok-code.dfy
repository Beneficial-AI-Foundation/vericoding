function abs(x: real): real
{
  if x < 0.0 then -x else x
}

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
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
    result := false;
  } else {
    result := false;
    var i := 0;
    while i < |numbers| && !result
      invariant 0 <= i <= |numbers|
      invariant !result && forall i' : int | 0 <= i' < i :: forall j' : int | i' < j' < |numbers| :: !(abs(numbers[i'] - numbers[j']) < threshold)
    {
      var j := i + 1;
      while j < |numbers| && !result
        invariant i + 1 <= j <= |numbers|
        invariant !result && forall j' : int | i < j' < j :: !(abs(numbers[i] - numbers[j']) < threshold)
      {
        if abs(numbers[i] - numbers[j]) < threshold {
          result := true;
          return;
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

