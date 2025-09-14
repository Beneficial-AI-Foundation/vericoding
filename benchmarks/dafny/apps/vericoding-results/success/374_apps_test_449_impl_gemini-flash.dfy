predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}

// <vc-helpers>
function Digits(n: int): seq<int>
    requires n >= 0
{
    if n == 0 then
        []
    else
        Digits(n / 10) + [n % 10]
}

lemma MinBillsLemma(n: int)
    requires n >= 1
    ensures MinBills(n) == n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 0
    ensures result == MinBills(n)
// </vc-spec>
// <vc-code>
{
    var num_100 := n / 100;
    var remainder_100 := n % 100;
    var num_20 := remainder_100 / 20;
    var remainder_20 := remainder_100 % 20;
    var num_10 := remainder_20 / 10;
    var remainder_10 := remainder_20 % 10;
    var num_5 := remainder_10 / 5;
    var remainder_5 := remainder_10 % 5;
    var num_1 := remainder_5;

    result := num_100 + num_20 + num_10 + num_5 + num_1;

    MinBillsLemma(n);
    assert result == MinBills(n);
}
// </vc-code>

