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
lemma XorAndProperties(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures xorOp(a, b) + 2 * andOp(a, b) == a + b
  decreases a + b
{
  if a == 0 || b == 0 {
  } else if a % 2 != b % 2 {
    XorAndProperties(a / 2, b / 2);
  } else if a % 2 == 1 {
    XorAndProperties(a / 2, b / 2);
  } else {
    XorAndProperties(a / 2, b / 2);
  }
}

lemma XorOpCommutes(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures xorOp(x, y) == xorOp(y, x)
  decreases x + y
{
  if x == 0 || y == 0 {
  } else {
    XorOpCommutes(x / 2, y / 2);
  }
}

lemma AndOpCommutes(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures andOp(x, y) == andOp(y, x)
  decreases x + y
{
  if x == 0 || y == 0 {
  } else {
    AndOpCommutes(x / 2, y / 2);
  }
}

lemma XorAssociative(x: int, y: int, z: int)
  requires x >= 0 && y >= 0 && z >= 0
  ensures xorOp(x, xorOp(y, z)) == xorOp(xorOp(x, y), z)
  decreases x + y + z
{
  if x == 0 {
  } else if y == 0 {
  } else if z == 0 {
  } else {
    XorAssociative(x / 2, y / 2, z / 2);
  }
}

lemma XorRangeProperties(a: seq<int>, start: int, end: int, index: int)
  requires 0 <= start <= index <= end <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures xorRange(a, start, end) == xorOp(xorRange(a, start, index), xorRange(a, index, end))
  decreases end - index
{
  if index == end {
  } else {
    XorRangeProperties(a, start, end, index + 1);
    XorAssociative(a[start], xorRange(a, start + 1, index), xorRange(a, index, end));
  }
}

lemma NimSumPositiveSummands(piles: seq<int>): bool
  requires forall i :: 0 <= i < |piles| ==> piles[i] >= 0
  ensures nimSum(piles) >= 0
{
  true
}

lemma findMaxPowerLemma(power: int, num: int)
  requires num >= 0
  requires power >= 1
  ensures findMaxPowerHelper(power, num) >= power
  decreases if power > num then 0 else num + 1 - power
{
  if power <= num {
    var next := power * 2;
    findMaxPowerLemma(next, num);
  }
}

lemma constructA0HelperLemma(a0: int, num: int, max_pile: int, power: int)
  requires a0 >= 0 && num >= 0 && power >= 1
  ensures constructA0Helper(a0, num, max_pile, power) >= a0 
       && constructA0Helper(a0, num, max_pile, power) <= a0 + power
{
  if power > 1 {
    var new_a0 := if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0;
    if power / 2 >= 1 {
      constructA0HelperLemma(new_a0, num, max_pile, power / 2);
    }
  }
}

lemma constructA0PreservesAnd(a0: int, num: int, max_pile: int, power: int)
  requires a0 >= 0 && num >= 0 && power >= 1
  requires andOp(a0, num) == 0
  ensures andOp(constructA0Helper(a0, num, max_pile, power), num) == 0
  decreases power
{
  if power > 1 {
    var new_a0 := if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0;
    assert andOp(new_a0, num) == 0;
    if power / 2 >= 1 {
      constructA0PreservesAnd(new_a0, num, max_pile, power / 2);
    }
  }
}

lemma constructA0HasXor(a0: int, num: int, max_pile: int, power: int)
  requires a0 >= 0 && num >= 0 && power >= 1
  requires andOp(a0, num) == 0
  ensures xorOp(constructA0Helper(a0, num, max_pile, power), num) == constructA0Helper(a0, num, max_pile, power) + num
  decreases power
{
  if power > 1 {
    var new_a0 := if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0;
    assert andOp(new_a0, num) == 0;
    if power / 2 >= 1 {
      constructA0HasXor(new_a0, num, max_pile, power / 2);
    }
  }
}

lemma XorAndDecomposition(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures xorOp(x, y) + 2 * andOp(x, y) == x + y
  decreases x + y
{
  if x == 0 || y == 0 {
  } else {
    XorAndDecomposition(x / 2, y / 2);
  }
}

lemma AndOpZero(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures andOp(x, y) == 0
  ensures xorOp(x, y) == x + y
  decreases x + y
{
}

lemma XorOpAssociative(x: int, y: int, z: int)
  requires x >= 0 && y >= 0 && z >= 0
  ensures xorOp(x, xorOp(y, z)) == xorOp(xorOp(x, y), z)
  decreases x + y + z
{
}

lemma MaximumConstructA0(a0: int, num: int, max_pile: int, power: int)
  requires a0 >= 0 && num >= 0 && power >= 1
  ensures constructA0Helper(a0, num, max_pile, power) <= max_pile
  decreases power
{
  if power > 1 {
    var new_a0 := if andOp(num, power) != 0 && a0 + power <= max_pile then a0 + power else a0;
    if power / 2 >= 1 {
      MaximumConstructA0(new_a0, num, max_pile, power / 2);
    }
  }
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
    if a[0] < a[1] || (a[0] - a[1]) % 2 != 0 {
      result := "-1";
    } else {
      result := intToStringFunc((a[0] - a[1]) / 2);
    }
  } else {
    var xor_total := xorRange(a, 2, n);
    var sum_val := a[0] + a[1];
    var and_val := sum_val - xor_total;
    
    if and_val % 2 != 0 || a[0] < and_val / 2 || andOp(and_val / 2, xor_total) != 0 {
      result := "-1";
    } else {
      var target_and := and_val / 2;
      var a0 := constructA0(target_and, xor_total, a[0]);
      if a0 == 0 || a0 > a[0] {
        result := "-1";
      } else {
        result := intToStringFunc(a[0] - a0);
      }
    }
  }
}
// </vc-code>

