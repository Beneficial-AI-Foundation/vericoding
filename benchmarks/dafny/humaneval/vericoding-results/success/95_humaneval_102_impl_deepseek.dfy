// <vc-preamble>

predicate ValidInput(x: int, y: int) {
    x > 0 && y > 0
}

predicate NoEvenInRange(x: int, y: int) {
    forall i :: x <= i <= y ==> i % 2 != 0
}

predicate IsLargestEvenInRange(x: int, y: int, result: int) {
    result % 2 == 0 && 
    x <= result <= y && 
    (forall i :: x <= i <= y && i % 2 == 0 ==> i <= result)
}

predicate CorrectResult(x: int, y: int, result: int) {
    if x > y then 
        result == -1
    else
        (result == -1 && NoEvenInRange(x, y)) ||
        IsLargestEvenInRange(x, y, result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed FindLargestEvenInRange termination and added decreasing clause */
function FindLargestEvenInRange(x: int, y: int): (r: int)
  requires ValidInput(x, y)
  requires exists i :: x <= i <= y && i % 2 == 0
  ensures IsLargestEvenInRange(x, y, r)
decreases y - x
{
  if y % 2 == 0 then y else FindLargestEvenInRange(x, y - 1)
}
// </vc-helpers>

// <vc-spec>
method ChooseNum(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures CorrectResult(x, y, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added verification of NoEvenInRange when no even numbers exist */
{
  if x > y {
    result := -1;
  } else {
    var hasEven := exists i :: x <= i <= y && i % 2 == 0;
    if hasEven {
      result := FindLargestEvenInRange(x, y);
    } else {
      result := -1;
      // Verify that no even numbers exist in range
      assert NoEvenInRange(x, y);
    }
  }
}
// </vc-code>
