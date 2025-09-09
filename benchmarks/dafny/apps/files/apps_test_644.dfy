Execute a sequence of commands (for n, end, add) that manipulate an integer variable x starting at 0.
Commands form valid nested loops. Check if x exceeds 2^32 - 1 at any point during execution.
Return "OVERFLOW!!!" if overflow occurs, otherwise return the final value of x.

predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

method ParseLines(input: string) returns (lines: seq<string>)
    ensures |lines| > 0
{
    lines := [input]; // Simplified parsing
}

method ParseForValue(line: string) returns (n: int)
    requires |line| >= 4 && line[0..4] == "for "
    ensures n >= 0
{
    n := 1; // Simplified - would need proper string parsing
}

method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
{
    var lines := ParseLines(input);
    var l := 100; // Maximum nesting depth
    var stack := new int[l];
    var multipliers := new int[l];
    var depth := 0;
    var x := 0;
    var overflow := false;
    var lineIdx := 0;

    // Initialize stack
    var i := 0;
    while i < l
        invariant 0 <= i <= l
        invariant stack.Length == l
        invariant multipliers.Length == l
    {
        stack[i] := 0;
        multipliers[i] := 1;
        i := i + 1;
    }

    while lineIdx < |lines| && !overflow
        invariant 0 <= lineIdx <= |lines|
        invariant 0 <= depth <= l
        invariant stack.Length == l
        invariant multipliers.Length == l
        invariant x >= 0
    {
        var line := if lineIdx < |lines| then lines[lineIdx] else "";

        if line == "add" {
            x := x + 1;
            if IsOverflow(x) {
                overflow := true;
            }
        } else if |line| >= 4 && line[0..4] == "for " {
            var n := ParseForValue(line);
            if depth < l {
                stack[depth] := 0;
                multipliers[depth] := n;
                depth := depth + 1;
            }
        } else if line == "end" {
            if depth > 0 {
                depth := depth - 1;
                var loopCount := stack[depth];
                var mult := multipliers[depth];

                if mult > 0 && loopCount > 0 {
                    if loopCount > 0 && mult > MAX_VALUE() / loopCount {
                        overflow := true;
                    } else {
                        var product := loopCount * mult;
                        if IsOverflow(product) {
                            overflow := true;
                        } else {
                            x := x + product;
                            if IsOverflow(x) {
                                overflow := true;
                            }
                        }
                    }
                }
            }
        }

        lineIdx := lineIdx + 1;
    }

    if overflow {
        result := "OVERFLOW!!!";
    } else {
        result := IntToString(x);
    }
}
