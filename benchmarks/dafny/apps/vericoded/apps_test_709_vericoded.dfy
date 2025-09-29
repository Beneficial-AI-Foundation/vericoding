function CountOnesInBinary(n: int): int
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 1 then 1 + CountOnesInBinary(n / 2)
    else CountOnesInBinary(n / 2)
}

predicate ValidInput(x: int) {
    x >= 1
}

predicate ValidOutput(x: int, result: int) {
    ValidInput(x) && result == CountOnesInBinary(x)
}

// <vc-helpers>
lemma CountOnesInBinaryCorrectness(n: int)
    requires n >= 1
    ensures n == 1 ==> CountOnesInBinary(n) == 1
    ensures n > 1 && n % 2 == 1 ==> CountOnesInBinary(n) == 1 + CountOnesInBinary(n / 2)
    ensures n > 1 && n % 2 == 0 ==> CountOnesInBinary(n) == CountOnesInBinary(n / 2)
{
    // This follows directly from the function definition
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var n := x;
    
    while n > 1
        invariant n >= 1
        invariant count + CountOnesInBinary(n) == CountOnesInBinary(x)
    {
        if n % 2 == 1 {
            count := count + 1;
        }
        n := n / 2;
    }
    
    // When n == 1, CountOnesInBinary(n) == 1
    count := count + 1;
    result := count;
}
// </vc-code>

