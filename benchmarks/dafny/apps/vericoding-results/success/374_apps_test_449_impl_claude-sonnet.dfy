predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 0
    ensures result == MinBills(n)
// </vc-spec>
// <vc-code>
{
    var hundreds := n / 100;
    var remainder_after_hundreds := n % 100;
    
    var twenties := remainder_after_hundreds / 20;
    var remainder_after_twenties := remainder_after_hundreds % 20;
    
    var tens := remainder_after_twenties / 10;
    var remainder_after_tens := remainder_after_twenties % 10;
    
    var fives := remainder_after_tens / 5;
    var ones := remainder_after_tens % 5;
    
    result := hundreds + twenties + tens + fives + ones;
}
// </vc-code>

