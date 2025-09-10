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
function MAX_VALUE_INT(): int { 4294967295 }

predicate IsOverflowInt(x: int)
{
    x > MAX_VALUE_INT()
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
    var num: int;
    if int.TryParse(input, out num)
    {
        if IsOverflowInt(num)
        {
            result := "OVERFLOW!!!";
        }
        else
        {
            result := num as string;
        }
    }
    else
    {
        result := "INVALID INPUT";
    }
}
// </vc-code>

