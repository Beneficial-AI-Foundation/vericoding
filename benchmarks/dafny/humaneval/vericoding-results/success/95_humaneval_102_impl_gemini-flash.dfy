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
    result := -1;
    if x <= y {
        var i := y;
        while i >= x
            invariant x <= i <= y || i == x - 1
            invariant (forall k :: i < k <= y && k % 2 == 0 ==> k <= result)
            invariant i < y ==> (result == -1 || IsLargestEvenInRange(x, y, result)) // if we found an even number, result is the largest
        {
            if i % 2 == 0 {
                result := i;
                return;
            }
            i := i - 1;
        }
    }
}
// </vc-code>
