// <vc-preamble>
function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}
// </vc-preamble>

// <vc-helpers>
predicate InRange(numbers: seq<real>, i: int)
{
  0 <= i && i < |numbers|
}

predicate ValidPair(numbers: seq<real>, i: int, j: int)
{
  InRange(numbers, i) && InRange(numbers, j) && i != j
}

predicate Close(x: real, y: real, threshold: real)
{
  threshold > 0.0 && abs(x - y) < threshold
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)

  requires threshold > 0.0

  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
// </vc-spec>
// <vc-code>
{
  flag := exists i: int, j: int ::
              i >= 0 && j >= 0 &&
              i < |numbers| && j < |numbers| &&
              i != j &&
              (if 0 <= i && i < |numbers| && 0 <= j && j < |numbers| then abs(numbers[i] - numbers[j]) < threshold else false);
}
// </vc-code>
