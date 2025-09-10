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
    if int.TryParse(input, out num) {
        if IsOverflowInt(num) {
            result := "OVERFLOW!!!";
        } else {
            result := input;
        }
    } else {
        // This case should ideally not happen if input is guaranteed to be a valid number string.
        // However, based on the `ValidInput([input])` predicate and generic string input,
        // we need to handle non-parseable inputs. The prompt's focus is on overflow.
        // For simplicity and to pass existing checks, we can return the input itself or a specific error.
        // Let's return "INVALID INPUT" for clarity if it's not a number.
        result := "INVALID INPUT";
    }
}
// </vc-code>

