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
lemma validatePizzaSolutionLemma(pizzas: seq<int>, index: int, d: bool, p: int, index2: int, d2: bool, p2: int)
    requires 0 <= index <= |pizzas|
    requires 0 <= index2 <= |pizzas|
    requires p == 0 || p == 1
    requires p2 == 0 || p2 == 1
    requires index <= index2
    decreases |pizzas| - index
    ensures validatePizzaSolution(pizzas, index, d, p) == validatePizzaSolution(pizzas, index2, d2, p2) 
{
    if index < index2 {
        var requirement := pizzas[index];
        var newP := if requirement % 2 == 1 then 1 - p else p;
        var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
        validatePizzaSolutionLemma(pizzas, index + 1, newD, newP, index2, d2, p2);
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
    var d := true;
    var p := 0;
    var i := 0;
    
    while i < |pizzas|
        invariant 0 <= i <= |pizzas|
        invariant p == 0 || p == 1
        invariant validatePizzaSolution(pizzas, 0, true, 0) == validatePizzaSolution(pizzas, i, d, p)
    {
        var requirement := pizzas[i];
        if requirement % 2 == 1 {
            p := 1 - p;
        }
        if requirement % 2 == 0 && p == 1 && requirement == 0 {
            d := false;
        }
        i := i + 1;
    }
    
    if d && p == 0 {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

