// <vc-preamble>
// ======= TASK =======
// Given two positive integers x and y, find the largest even integer in the range [x, y] inclusive.
// If no even integer exists in this range, return -1.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method ChooseNum(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures CorrectResult(x, y, result)
// </vc-spec>
// <vc-code>
{
    if x > y {
        result := -1;
    } else if y % 2 == 0 {
        result := y;
    } else if y - 1 >= x {
        result := y - 1;
    } else {
        result := -1;
    }
}
// </vc-code>
