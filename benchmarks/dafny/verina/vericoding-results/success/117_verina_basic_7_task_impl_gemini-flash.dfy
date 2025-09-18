// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function square(x: nat): nat { x * x }
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3
    {
        // The i-th odd number is 2*i + 1 (starting from 0-indexed i)
        // The (i+1)-th odd number is 2*(i) + 1 (using 1-indexed i)
        // To match the formula in the invariant, which is for 'i' numbers, 
        // we need to add the square of the (i+1)-th odd number, which corresponds to 2*i + 1.
        
        var currentOddNumber := 2*i + 1;
        result := result + square(currentOddNumber);
        i := i + 1;
    }
}
// </vc-code>
