predicate validInput(s: string)
{
    var lines := splitLinesFunc(s);
    |lines| >= 2 && 
    parseIntFunc(lines[0]) >= 2 &&
    |parseIntArrayFunc(lines[1])| == parseIntFunc(lines[0]) &&
    forall i :: 0 <= i < |parseIntArrayFunc(lines[1])| ==> parseIntArrayFunc(lines[1])[i] >= 1
}

predicate isValidOutput(s: string)
{
    s == "-1" || (parseIntFunc(s) >= 0)
}

predicate correctSolution(input: string, output: string)
{
    var lines := splitLinesFunc(input);
    |lines| >= 2 ==>
    var n := parseIntFunc(lines[0]);
    var a := parseIntArrayFunc(lines[1]);

    if n == 2 then
        (output == "-1" <==> (a[0] < a[1] || (a[0] - a[1]) % 2 != 0)) &&
        (output != "-1" ==> parseIntFunc(output) == (a[0] - a[1]) / 2)
    else
        var xor_rest := xorRange(a, 2, n);
        var and_val := a[0] + a[1] - xor_rest;
        var target_and := and_val / 2;

        if and_val % 2 != 0 || a[0] < target_and || andOp(target_and, xor_rest) != 0 then
            output == "-1"
        else
            var a0 := constructA0(target_and, xor_rest, a[0]);
            if a0 == 0 then
                output == "-1"
            else
                output != "-1" && parseIntFunc(output) == a[0] - a0
}

predicate secondPlayerWins(original_piles: seq<int>, stones_moved: int)
  requires |original_piles| >= 2
  requires 0 <= stones_moved < original_piles[0]
  requires forall i :: 0 <= i < |original_piles| ==> original_piles[i] >= 0
{
    var new_piles := original_piles[0 := original_piles[0] - stones_moved][1 := original_piles[1] + stones_moved];
    nimSum(new_piles) == 0
}

function nimSum(piles: seq<int>): int
  requires forall i :: 0 <= i < |piles| ==> piles[i] >= 0
  ensures nimSum(piles) >= 0
{
    if |piles| == 0 then 0
    else xorOp(piles[0], nimSum(piles[1..]))
}

function xorOp(x: int, y: int): int
  requires x >= 0 && y >= 0
  ensures xorOp(x, y) >= 0
  decreases x + y
{
    if x == 0 then y
    else if y == 0 then x
    else if x % 2 != y % 2 then 1 + 2 * xorOp(x / 2, y / 2)
    else 2 * xorOp(x / 2, y / 2)
}

function andOp(x: int, y: int): int
  requires x >= 0 && y >= 0
  ensures andOp(x, y) >= 0
  decreases x + y
{
    if x == 0 || y == 0 then 0
    else if x % 2 == 1 && y % 2 == 1 then 1 + 2 * andOp(x / 2, y / 2)
    else 2 * andOp(x / 2, y / 2)
}

function xorRange(a: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures xorRange(a, start, end) >= 0
  decreases end - start
{
    if start >= end then 0
    else xorOp(a[start], xorRange(a, start + 1, end))
}

function constructA0(initial_and: int, num: int, max_pile: int): int
  requires initial_and >= 0
  requires num >= 0
{
    var max_power := findMaxPower(num);
    constructA0Helper(initial_and, num, max_pile, max_power)
}

function findMaxPower(num: int): int
  requires num >= 0
  ensures findMaxPower(num) >= 1
{
    if num == 0 then 1
    else
        var power := 1;
        findMaxPowerHelper(power, num)
}

function findMaxPowerHelper(current_power: int, num: int): int
  requires current_power >= 1
  requires num >= 0
  ensures findMaxPowerHelper(current_power, num) >= 1
  decreases if current_power > num then 0 else num + 1 - current_power
{
    if current_power > num then 
        if current_power / 2 >= 1 then current_power / 2 else 1
    else findMaxPowerHelper(current_power * 2, num)
}

function constructA0Helper(a0: int, num: int, max_pile: int, power: int): int
  requires a0 >= 0
  requires num >= 0
  requires power >= 1
  decreases power
{
    if power == 1 then 
        if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0
    else
        var new_a0 := if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0;
        if power / 2 >= 1 then constructA0Helper(new_a0, num, max_pile, power / 2) else new_a0
}

function splitLinesFunc(s: string): seq<string>
{
    [s]
}

function parseIntFunc(s: string): int
{
    0
}

function parseIntArrayFunc(s: string): seq<int>
{
    []
}

function intToStringFunc(n: int): string
{
    "0"
}

// <vc-helpers>
lemma XorProperties(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures xorOp(x, x) == 0
    ensures xorOp(x, y) == xorOp(y, x)
    ensures xorOp(x, 0) == x
    decreases x + y
{
    if x == 0 {
        assert xorOp(0, 0) == 0;
        assert xorOp(0, y) == y;
    } else if y == 0 {
        assert xorOp(x, 0) == x;
    } else if x == y {
        // When x == y, we need to prove xorOp(x, x) == 0
        if x % 2 == 0 {
            // Both even: xorOp(x, x) = 2 * xorOp(x/2, x/2)
            XorProperties(x / 2, x / 2);
            assert xorOp(x / 2, x / 2) == 0;
            assert xorOp(x, x) == 2 * xorOp(x / 2, x / 2) == 2 * 0 == 0;
        } else {
            // Both odd: xorOp(x, x) = 2 * xorOp(x/2, x/2)
            XorProperties(x / 2, x / 2);
            assert xorOp(x / 2, x / 2) == 0;
            assert x % 2 == 1;
            assert x % 2 == x % 2;
            assert !(x % 2 != x % 2);
            assert xorOp(x, x) == 2 * xorOp(x / 2, x / 2) == 2 * 0 == 0;
        }
    } else {
        XorProperties(x / 2, y / 2);
        if x % 2 != y % 2 {
            assert xorOp(x, y) == 1 + 2 * xorOp(x / 2, y / 2);
            assert xorOp(y, x) == 1 + 2 * xorOp(y / 2, x / 2);
            assert xorOp(x / 2, y / 2) == xorOp(y / 2, x / 2);
        } else {
            assert xorOp(x, y) == 2 * xorOp(x / 2, y / 2);
            assert xorOp(y, x) == 2 * xorOp(y / 2, x / 2);
            assert xorOp(x / 2, y / 2) == xorOp(y / 2, x / 2);
        }
    }
}

lemma NimSumXorEquivalence(piles: seq<int>, start: int, end: int)
    requires forall i :: 0 <= i < |piles| ==> piles[i] >= 0
    requires 0 <= start <= end <= |piles|
    ensures start < end ==> xorRange(piles, start, end) == xorOp(piles[start], xorRange(piles, start + 1, end))
{
    // This follows directly from the definition
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires validInput(stdin_input)
  ensures |result| > 0
  ensures isValidOutput(result)
  ensures result == "-1" || (parseIntFunc(result) >= 0)
  ensures correctSolution(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var lines := splitLinesFunc(stdin_input);
    var n := parseIntFunc(lines[0]);
    var a := parseIntArrayFunc(lines[1]);
    
    if n == 2 {
        // Special case for n = 2
        if a[0] < a[1] || (a[0] - a[1]) % 2 != 0 {
            result := "-1";
        } else {
            var stones_moved := (a[0] - a[1]) / 2;
            result := intToStringFunc(stones_moved);
        }
    } else {
        // General case for n > 2
        var xor_rest := xorRange(a, 2, n);
        var and_val := a[0] + a[1] - xor_rest;
        var target_and := and_val / 2;
        
        if and_val % 2 != 0 || a[0] < target_and || andOp(target_and, xor_rest) != 0 {
            result := "-1";
        } else {
            var a0 := constructA0(target_and, xor_rest, a[0]);
            if a0 == 0 {
                result := "-1";
            } else {
                var stones_moved := a[0] - a0;
                result := intToStringFunc(stones_moved);
            }
        }
    }
}
// </vc-code>

