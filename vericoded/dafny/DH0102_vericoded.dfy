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

// </vc-helpers>

// <vc-spec>
method ChooseNum(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures CorrectResult(x, y, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed decreases clause to handle both conditions */
  if x > y {
    result := -1;
  } else {
    result := -1;
    var found := false;
    var i := y;
    while i >= x && !found
      decreases if found then 0 else i - x + 1
      invariant x - 1 <= i <= y
      invariant !found ==> result == -1
      invariant !found ==> forall j :: i < j <= y ==> j % 2 != 0
      invariant found ==> result % 2 == 0 && x <= result <= y
      invariant found ==> forall j :: result < j <= y ==> j % 2 != 0
      invariant found ==> IsLargestEvenInRange(x, y, result)
    {
      if i % 2 == 0 {
        result := i;
        found := true;
      } else {
        i := i - 1;
      }
    }
    assert !found ==> i < x;
    assert !found ==> forall j :: x <= j <= y ==> j % 2 != 0;
  }
}
// </vc-code>
