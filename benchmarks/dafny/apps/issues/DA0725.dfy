// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    exists lines :: 
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        exists n, q ::
            ParseFirstLine(lines[0]) == (n, q) &&
            1 <= n <= 50 && 0 <= q <= 100 &&
            |lines| == q + 1 &&
            (forall i :: 1 <= i <= q ==> ValidConstraintLine(lines[i], n))
}

function SplitLines(input: string): seq<string>
{
    [""] // Placeholder
}

function ParseFirstLine(line: string): (nat, nat)
{
    (1, 0) // Placeholder
}

predicate ValidConstraintLine(line: string, n: nat)
{
    exists t, l, r, v ::
        ParseConstraintLine(line) == (t, l, r, v) &&
        t in {1, 2} && 1 <= l <= r <= n && 1 <= v <= n
}

function ParseConstraintLine(line: string): (nat, nat, nat, nat)
{
    (1, 1, 1, 1) // Placeholder
}

function ParseInput(input: string): (nat, nat, seq<(nat, nat, nat, nat)>)
    requires ValidInputFormat(input)
    ensures var parsed := ParseInput(input);
            var n := parsed.0; var q := parsed.1; var constraints := parsed.2;
            1 <= n <= 50 && 0 <= q <= 100 && |constraints| == q
{
    var lines := SplitLines(input);
    var firstLineParsed := ParseFirstLine(lines[0]);
    var n := firstLineParsed.0;
    var q := firstLineParsed.1;
    var constraints := if q == 0 then [] else seq(q, i requires 0 <= i < q && i+1 < |lines| => ParseConstraintLine(lines[i+1]));
    (n, q, constraints)
}

function BuildBounds(n: nat, constraints: seq<(nat, nat, nat, nat)>): (seq<nat>, seq<nat>)
    requires n > 0
    requires forall c :: c in constraints ==> 
        var t := c.0; var l := c.1; var r := c.2; var v := c.3;
        t in {1, 2} && 1 <= l <= r <= n && 1 <= v <= n
    ensures var bounds := BuildBounds(n, constraints);
            var geq := bounds.0; var leq := bounds.1;
            |geq| == n && |leq| == n
    ensures var bounds := BuildBounds(n, constraints);
            var geq := bounds.0; var leq := bounds.1;
            forall i :: 0 <= i < n ==> 0 <= geq[i] <= n-1 && 0 <= leq[i] <= n-1
{
    var geq := seq(n, i => 0);
    var leq := seq(n, i => n-1);
    ApplyConstraints(geq, leq, constraints)
}

predicate HasContradiction(n: nat, geq: seq<nat>, leq: seq<nat>)
    requires n > 0
    requires |geq| == n && |leq| == n
{
    exists i :: 0 <= i < n && geq[i] > leq[i]
}

function MinimumCostSolution(n: nat, geq: seq<nat>, leq: seq<nat>): nat
    requires n > 0
    requires |geq| == n && |leq| == n
    requires !HasContradiction(n, geq, leq)
    requires forall i :: 0 <= i < n ==> 0 <= geq[i] <= leq[i] <= n-1
{
    0  // Placeholder
}
// </vc-preamble>

// <vc-helpers>
function ApplyConstraints(geq: seq<nat>, leq: seq<nat>, constraints: seq<(nat, nat, nat, nat)>): (seq<nat>, seq<nat>)
    requires |geq| == |leq|
    requires forall c :: c in constraints ==> 
        var t := c.0; var l := c.1; var r := c.2; var v := c.3;
        t in {1, 2} && 1 <= l <= r <= |geq| && 1 <= v <= |geq|
    ensures var result := ApplyConstraints(geq, leq, constraints);
            |result.0| == |geq| && |result.1| == |leq|
{
    (geq, leq) // Placeholder
}

function nat_to_string(n: nat): string
{
    if n == 0 then "0"
    else nat_to_string_helper(n)
}

function nat_to_string_helper(n: nat): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else nat_to_string_helper(n / 10) + [('0' as int + (n % 10)) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n'
    requires ValidInputFormat(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == "-1\n" || 
            (|result| >= 2 && result[|result|-1] == '\n' && 
             forall i :: 0 <= i < |result|-1 ==> result[i] in "0123456789")
    ensures result == "-1\n" || 
            (exists val: nat :: result == nat_to_string(val) + "\n")
    ensures ValidInputFormat(stdin_input) ==>
            (var parsed := ParseInput(stdin_input);
             var n := parsed.0;
             var q := parsed.1; 
             var constraints := parsed.2;
             var bounds := BuildBounds(n, constraints);
             var geq := bounds.0;
             var leq := bounds.1;
             if HasContradiction(n, geq, leq) then result == "-1\n"
             else (exists cost: nat :: result == nat_to_string(cost) + "\n" && 
                  cost == MinimumCostSolution(n, geq, leq)))
    ensures ValidInputFormat(stdin_input) ==>
            (var parsed := ParseInput(stdin_input);
             var n := parsed.0;
             var q := parsed.1;
             var constraints := parsed.2;
             n >= 1 && n <= 50 && q >= 0 && q <= 100 &&
             |constraints| == q &&
             (forall c :: c in constraints ==> 
                var t := c.0; var l := c.1; var r := c.2; var v := c.3;
                t in
// </vc-spec>
// <vc-code>
{1, 2}
// </vc-code>
