// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): complete rebuild with proper verification */
function BuildResult(numbers: seq<int>, delimeter: int): seq<int>
  ensures |numbers| != 0 ==> |BuildResult(numbers, delimeter)| == |numbers| * 2 - 1
  ensures |numbers| == 0 ==> |BuildResult(numbers, delimeter)| == 0
  ensures forall i : int :: i >= 0 && i < |BuildResult(numbers, delimeter)| && i % 2 == 0 ==> BuildResult(numbers, delimeter)[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |BuildResult(numbers, delimeter)| && i % 2 == 1 ==> BuildResult(numbers, delimeter)[i] == delimeter
{
  if |numbers| == 0 then []
  else if |numbers| == 1 then [numbers[0]]
  else [numbers[0], delimeter] + BuildResult(numbers[1..], delimeter)
}
// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)

  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): simplified implementation using verified helper */
{
  res := BuildResult(numbers, delimeter);
}
// </vc-code>
