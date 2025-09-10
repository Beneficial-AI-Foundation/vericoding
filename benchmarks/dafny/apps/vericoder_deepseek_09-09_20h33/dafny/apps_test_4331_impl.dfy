predicate ValidInput(N: int) {
    100 <= N <= 999
}

predicate ContainsSeven(N: int) 
    requires ValidInput(N)
{
    (N % 10) == 7 || ((N / 10) % 10) == 7 || (N / 100) == 7
}

predicate ValidOutput(result: string) {
    result == "Yes\n" || result == "No\n"
}

// <vc-helpers>
lemma ModSevenLemma(n: int, divisor: int)
    requires 100 <= n <= 999
    requires divisor == 1 || divisor == 10 || divisor == 100
    ensures (n / divisor) % 10 == 7 <==> (n / divisor) % 10 == 7
{
}

lemma DivisionLemma(n: int, divisor: int)
    requires 100 <= n <= 999
    requires divisor == 1 || divisor == 10 || divisor == 100
    ensures 0 <= (n / divisor) % 10 <= 9
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures ValidOutput(result)
    ensures result == "Yes\n" <==> ContainsSeven(N)
// </vc-spec>
// <vc-code>
{
    var units := N % 10;
    var tens := (N / 10) % 10;
    var hundreds := N / 100;
    
    if units == 7 || tens == 7 || hundreds == 7 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

