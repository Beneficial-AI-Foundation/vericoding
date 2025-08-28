function abs(x: real): real
{
  if x < 0.0 then -x else x
}

// <vc-helpers>
lemma AbsDifferenceProperties(x: real, y: real)
  ensures abs(x - y) == abs(y - x)
  ensures abs(x - y) >= 0.0
{
  if (x - y) < 0.0 {
    calc {
      abs(x - y);
      -(x - y);
      y - x;
      abs(y - x);
    }
  } else {
    calc {
      abs(x - y);
      x - y;
      abs(y - x);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
// </vc-spec>
// </vc-spec>

// <vc-code>
method HasCloseElements(numbers: seq<real>, threshold: real) returns (result: bool)
  ensures result <==> exists i, j ::
    0 <= i < |numbers| &&
    0 <= j < |numbers| &&
    i != j &&
    abs(numbers[i] - numbers[j]) < threshold
  ensures result ==> |numbers| > 1
{
  if |numbers| <= 1 {
    return false;
  }
  
  result := false;
  var i := 0;
  while i < |numbers| - 1
    invariant 0 <= i < |numbers|
    invariant result ==> exists k, l ::
      0 <= k < |numbers| &&
      0 <= l < |numbers| &&
      k != l &&
      abs(numbers[k] - numbers[l]) < threshold
    invariant !result ==> forall k, l ::
      0 <= k < i &&
      0 <= l < |numbers| &&
      k != l ==> 
      abs(numbers[k] - numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < |numbers|
      invariant 0 <= i < j <= |numbers|
      invariant result ==> exists k, l ::
        0 <= k < |numbers| &&
        0 <= l < |numbers| &&
        k != l &&
        abs(numbers[k] - numbers[l]) < threshold
      invariant !result ==> forall k, l ::
        0 <= k < i &&
        0 <= l < |numbers| &&
        k != l ==> 
        abs(numbers[k] - numbers[l]) >= threshold
      invariant !result ==> forall l ::
        i < l < j ==> 
        abs(numbers[i] - numbers[l]) >= threshold
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>
