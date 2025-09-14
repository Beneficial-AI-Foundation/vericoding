predicate ValidInput(pizzas: seq<int>) {
    forall i :: 0 <= i < |pizzas| ==> pizzas[i] >= 0
}

function validatePizzaSolution(pizzas: seq<int>, index: int, d: bool, p: int): bool
    requires 0 <= index <= |pizzas|
    requires p == 0 || p == 1
    decreases |pizzas| - index
{
    if index == |pizzas| then
        d && p == 0
    else
        var requirement := pizzas[index];
        var newP := if requirement % 2 == 1 then 1 - p else p;
        var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
        validatePizzaSolution(pizzas, index + 1, newD, newP)
}

predicate CanFulfillRequirements(pizzas: seq<int>) {
    validatePizzaSolution(pizzas, 0, true, 0)
}

// <vc-helpers>
lemma ValidatePizzaSolutionCorrectness(pizzas: seq<int>, index: int, d: bool, p: int)
    requires 0 <= index <= |pizzas|
    requires p == 0 || p == 1
    ensures validatePizzaSolution(pizzas, index, d, p) == validatePizzaSolution(pizzas, index, d, p)
{
}

function computeSolution(pizzas: seq<int>, index: int, d: bool, p: int): bool
    requires 0 <= index <= |pizzas|
    requires p == 0 || p == 1
    decreases |pizzas| - index
{
    if index == |pizzas| then
        d && p == 0
    else
        var requirement := pizzas[index];
        var newP := if requirement % 2 == 1 then 1 - p else p;
        var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
        computeSolution(pizzas, index + 1, newD, newP)
}

lemma ComputeSolutionEqualsValidate(pizzas: seq<int>, index: int, d: bool, p: int)
    requires 0 <= index <= |pizzas|
    requires p == 0 || p == 1
    ensures computeSolution(pizzas, index, d, p) == validatePizzaSolution(pizzas, index, d, p)
    decreases |pizzas| - index
{
    if index == |pizzas| {
    } else {
        var requirement := pizzas[index];
        var newP := if requirement % 2 == 1 then 1 - p else p;
        var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
        ComputeSolutionEqualsValidate(pizzas, index + 1, newD, newP);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(pizzas: seq<int>) returns (result: string)
    requires ValidInput(pizzas)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanFulfillRequirements(pizzas)
// </vc-spec>
// <vc-code>
{
    var canFulfill := computeSolution(pizzas, 0, true, 0);
    ComputeSolutionEqualsValidate(pizzas, 0, true, 0);
    if canFulfill {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

