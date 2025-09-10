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
lemma CountOnesInBinaryLemma(n: int)
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n > 1 {
        if n % 2 == 1 {
            CountOnesInBinaryLemma(n / 2);
        } else {
            CountOnesInBinaryLemma(n / 2);
        }
    }
}

function CountOnes(n: int): int
    decreases n
{
    if n == 0 then 0
    else (n % 2) + CountOnes(n / 2)
}

lemma CountOnesInBinaryLemma2(n: int)
    requires n >= 1
    ensures CountOnesInBinary(n) == CountOnes(n)
    decreases n
{
    if n > 1 {
        if n % 2 == 1 {
            CountOnesInBinaryLemma2(n / 2);
        } else {
            CountOnesInBinaryLemma2(n / 2);
        }
    }
}

lemma CountOnesProperties(n: int)
    requires n >= 1
    ensures CountOnes(n) <= n
    decreases n
{
    if n > 1 {
        CountOnesProperties(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var current := x;
    
    while (current > 0)
        invariant current >= 0
        invariant result == CountOnes(x) - CountOnes(current)
        decreases current
    {
        result := result + (current % 2);
        current := current / 2;
    }
}
// </vc-code>

