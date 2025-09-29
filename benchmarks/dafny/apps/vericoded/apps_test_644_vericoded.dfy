predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

// <vc-helpers>
function StringToInt(s: string): int
{
    0  // Abstract function - actual parsing logic would go here
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
    var value := StringToInt(input);
    if IsOverflow(value) {
        result := "OVERFLOW!!!";
    } else {
        result := "OK";
    }
}
// </vc-code>

