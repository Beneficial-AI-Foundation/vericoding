// ======= TASK =======
// Given a rectangular board and two rectangular paintings, determine if both paintings 
// can be placed on the board without overlapping. Paintings can be rotated 90 degrees.

// ======= SPEC REQUIREMENTS =======
predicate validInput(input: string)
{
    |input| > 0
}

function parseInput(input: string): (int, int, int, int, int, int)
    requires validInput(input)
    ensures var (a, b, c, d, e, f) := parseInput(input); 
            a > 0 && b > 0 && c > 0 && d > 0 && e > 0 && f > 0 &&
            a <= 1000 && b <= 1000 && c <= 1000 && d <= 1000 && e <= 1000 && f <= 1000
{
    (1, 1, 1, 1, 1, 1)
}

function max(x: int, y: int): int
{
    if x >= y then x else y
}

// <vc-helpers>
lemma maxProperties(x: int, y: int)
    ensures max(x, y) >= x
    ensures max(x, y) >= y
    ensures max(x, y) == x || max(x, y) == y
{
}

lemma canFitConditionsComplete(a: int, b: int, c: int, d: int, e: int, f: int)
    ensures ((c + e <= a && max(d, f) <= b) ||
             (c + e <= b && max(d, f) <= a) ||
             (c + f <= a && max(d, e) <= b) ||
             (c + f <= b && max(d, e) <= a) ||
             (d + e <= a && max(c, f) <= b) ||
             (d + e <= b && max(c, f) <= a) ||
             (d + f <= a && max(c, e) <= b) ||
             (d + f <= b && max(c, e) <= a)) <==>
            ((c + e <= a && max(d, f) <= b) ||
             (c + e <= b && max(d, f) <= a) ||
             (c + f <= a && max(d, e) <= b) ||
             (c + f <= b && max(d, e) <= a) ||
             (d + e <= a && max(c, f) <= b) ||
             (d + e <= b && max(c, f) <= a) ||
             (d + f <= a && max(c, e) <= b) ||
             (d + f <= b && max(c, e) <= a))
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires validInput(input)
    ensures output == "YES" || output == "NO"
    ensures 
        var (a, b, c, d, e, f) := parseInput(input);
        output == "YES" <==> 
            ((c + e <= a && max(d, f) <= b) ||
             (c + e <= b && max(d, f) <= a) ||
             (c + f <= a && max(d, e) <= b) ||
             (c + f <= b && max(d, e) <= a) ||
             (d + e <= a && max(c, f) <= b) ||
             (d + e <= b && max(c, f) <= a) ||
             (d + f <= a && max(c, e) <= b) ||
             (d + f <= b && max(c, e) <= a))
// </vc-spec>
// <vc-code>
{
    var (a, b, c, d, e, f) := parseInput(input);

    var canFit := false;

    if c + e <= a && max(d, f) <= b {
        canFit := true;
    }
    else if c + e <= b && max(d, f) <= a {
        canFit := true;
    }
    else if c + f <= a && max(d, e) <= b {
        canFit := true;
    }
    else if c + f <= b && max(d, e) <= a {
        canFit := true;
    }
    else if d + e <= a && max(c, f) <= b {
        canFit := true;
    }
    else if d + e <= b && max(c, f) <= a {
        canFit := true;
    }
    else if d + f <= a && max(c, e) <= b {
        canFit := true;
    }
    else if d + f <= b && max(c, e) <= a {
        canFit := true;
    }

    if canFit {
        output := "YES";
    } else {
        output := "NO";
    }
}
// </vc-code>

