function abs(x: real): real
{
  if x < 0.0 then -x else x
}

// <vc-helpers>
lemma twoDistinctIndicesRequireLengthAtLeastTwo(len: int, i: int, j: int)
  requires 0 <= i < len
  requires 0 <= j < len
  requires i != j
  ensures len > 1
{
  if i < j {
    assert i + 1 <= j;
    assert 1 <= j;
    assert j + 1 <= len;
    assert 2 <= len;
    assert len > 1;
  } else {
    assert j < i;
    assert j + 1 <= i;
    assert 1 <= i;
    assert i + 1 <= len;
    assert 2 <= len;
    assert len > 1;
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
  result := exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold;
  if result {
    var i: int, j: int :|
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold;
    twoDistinctIndicesRequireLengthAtLeastTwo(|numbers|, i, j);
  }
}
// </vc-code>

