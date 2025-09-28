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
/* helper modified by LLM (iteration 2): added lemmas to help prove postcondition */
function max(a: int, b: int): int {
    if a >= b then a else b
}

lemma NoEvenExistsLemma(x: int, y: int)
    requires x <= y
    requires NoEvenInRange(x, y)
    ensures forall i :: x <= i <= y && i % 2 == 0 ==> false
{
}

lemma LargestEvenUniqueness(x: int, y: int, result1: int, result2: int)
    requires x <= y
    requires IsLargestEvenInRange(x, y, result1)
    requires IsLargestEvenInRange(x, y, result2)
    ensures result1 == result2
{
}

lemma HelperLemmaForCorrectness(x: int, y: int, result: int, finalI: int)
    requires x <= y
    requires finalI < x
    requires result == -1
    requires forall j :: finalI < j <= y && j % 2 == 0 ==> false
    ensures NoEvenInRange(x, y)
{
    forall i | x <= i <= y
        ensures i % 2 != 0
    {
        if i % 2 == 0 {
            assert finalI < i <= y;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method ChooseNum(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures CorrectResult(x, y, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop invariants and added assertion */
    if x > y {
        result := -1;
        return;
    }
    
    result := -1;
    var i := y;
    
    while i >= x
        invariant result == -1 || (result % 2 == 0 && i < result <= y)
        invariant result == -1 || (forall j :: result < j <= y && j % 2 == 0 ==> false)
        invariant result == -1 || (x <= result)
        invariant forall j :: i < j <= y && j % 2 == 0 ==> (result != -1 && j <= result)
        decreases i - x + 1
    {
        if i % 2 == 0 {
            result := i;
            break;
        }
        i := i - 1;
    }
    
    if result == -1 {
        HelperLemmaForCorrectness(x, y, result, i);
    }
}
// </vc-code>
