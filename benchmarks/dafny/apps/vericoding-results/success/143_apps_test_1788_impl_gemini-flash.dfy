predicate ValidInput(a: int, b: int)
{
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

predicate CorrectSolution(a: int, b: int, x: int, y: int)
{
    a == x + y && b == x - y
}

// <vc-helpers>
lemma ParityOfSumAndDifference(a: int, b: int)
    requires (a + b) % 2 == 0
    requires (a - b) % 2 == 0
    ensures (a % 2 == 0 && b % 2 == 0) || (a % 2 == 1 && b % 2 == 1)
{
    // (a + b) is even means a and b have the same parity
    // (a - b) is even means a and b have the same parity
    // This lemma essentially states that if the sum and difference of two integers are both even,
    // then the integers themselves must have the same parity (both even or both odd).
    // This is useful for recognizing that x and y derived using (a+b)/2 and (a-b)/2 will be integers.
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (x: int, y: int)
    requires ValidInput(a, b)
    ensures CorrectSolution(a, b, x, y)
// </vc-spec>
// <vc-code>
{
    var x_cand := (a + b) / 2;
    var y_cand := (a - b) / 2;

    // From the precondition ValidInput(a, b):
    // (a + b) % 2 == 0  implies (a + b) is even.
    // (a - b) % 2 == 0  implies (a - b) is even.
    // Therefore, both (a + b) / 2 and (a - b) / 2 will be integers.

    x := x_cand;
    y := y_cand;

    assert a == x + y by {
        calc {
            x + y;
            ((a + b) / 2) + ((a - b) / 2);
            // Since (a+b) and (a-b) are both even, integer division is exact.
            // (a + b + a - b) / 2;
            (2 * a) / 2;
            a;
        }
    }

    assert b == x - y by {
        calc {
            x - y;
            ((a + b) / 2) - ((a - b) / 2);
            // Since (a+b) and (a-b) are both even, integer division is exact.
            // (a + b - (a - b)) / 2;
            (a + b - a + b) / 2;
            (2 * b) / 2;
            b;
        }
    }
}
// </vc-code>

