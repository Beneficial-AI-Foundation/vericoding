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
    ensures validatePizzaSolution(pizzas, index, d, p) == 
            (if index == |pizzas| then d && p == 0
             else if index < |pizzas| && pizzas[index] % 2 == 1 then
                 validatePizzaSolution(pizzas, index + 1, d, 1 - p)
             else if index < |pizzas| && pizzas[index] == 0 && p == 1 then
                 validatePizzaSolution(pizzas, index + 1, false, p)
             else 
                 validatePizzaSolution(pizzas, index + 1, d, p))
    decreases |pizzas| - index
{
    // This follows directly from the function definition
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
    var i := 0;
    var parity := 0;
    var valid := true;
    
    while i < |pizzas|
        invariant 0 <= i <= |pizzas|
        invariant parity == 0 || parity == 1
        invariant validatePizzaSolution(pizzas, i, valid, parity) == CanFulfillRequirements(pizzas)
    {
        var requirement := pizzas[i];
        
        if requirement % 2 == 1 {
            parity := 1 - parity;
        } else if requirement == 0 && parity == 1 {
            valid := false;
        }
        
        i := i + 1;
    }
    
    if valid && parity == 0 {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

