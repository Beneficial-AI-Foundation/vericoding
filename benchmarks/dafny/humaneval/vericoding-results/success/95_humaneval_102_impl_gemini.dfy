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
  /* code modified by LLM (iteration 2): corrected lower bound of loop counter invariant */
  if x > y {
    result := -1;
    return;
  }

  var i := y;
  while i >= x
    decreases i
    invariant x - 1 <= i <= y
    invariant NoEvenInRange(i + 1, y)
  {
    if i % 2 == 0 {
      result := i;
      return;
    }
    i := i - 1;
  }

  result := -1;
}
// </vc-code>
