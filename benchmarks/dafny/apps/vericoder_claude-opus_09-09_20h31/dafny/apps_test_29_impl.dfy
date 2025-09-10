function charToInt(c: char): int
  requires '0' <= c <= '9'
{
  c as int - '0' as int
}

function isLucky(digits: seq<int>): bool
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  sum1 == sum2
}

predicate ValidTicket(ticket: string)
{
  |ticket| == 6 && forall i :: 0 <= i < |ticket| ==> '0' <= ticket[i] <= '9'
}

predicate canMakeLuckyWith0Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  isLucky(digits)
}

predicate canMakeLuckyWith1Change(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  exists pos :: 0 <= pos < 6 &&
    exists newDigit :: 0 <= newDigit <= 9 &&
      var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
      isLucky(newDigits)
}

predicate canMakeLuckyWith2Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  exists i, j :: 0 <= j < i < 6 &&
    exists k, l :: 0 <= k <= 9 && 0 <= l <= 9 &&
      var newDigits := digits[..i] + [k] + digits[i+1..];
      var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
      isLucky(finalDigits)
}

// <vc-helpers>
lemma canAlwaysMakeLuckyWith3Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures exists i, j, k :: 0 <= i < j < k < 6 &&
    exists a, b, c :: 0 <= a <= 9 && 0 <= b <= 9 && 0 <= c <= 9 &&
      var d1 := digits[..i] + [a] + digits[i+1..];
      var d2 := d1[..j] + [b] + d1[j+1..];
      var d3 := d2[..k] + [c] + d2[k+1..];
      |d3| == 6 && (forall idx :: 0 <= idx < |d3| ==> 0 <= d3[idx] <= 9) && isLucky(d3)
{
  // We'll change positions 0, 1, 2 to make the sum equal to the sum of positions 3, 4, 5
  var targetSum := digits[3] + digits[4] + digits[5];
  assert targetSum <= 27; // Maximum possible sum is 9+9+9=27
  
  // Distribute targetSum across three digits (each at most 9)
  var a := if targetSum <= 9 then targetSum else 9;
  var remainder1 := if targetSum <= 9 then 0 else targetSum - 9;
  var b := if remainder1 <= 9 then remainder1 else 9;
  var remainder2 := if remainder1 <= 9 then 0 else remainder1 - 9;
  var c := remainder2;
  
  assert 0 <= a <= 9;
  assert 0 <= b <= 9;
  assert 0 <= c <= 9;
  assert a + b + c == targetSum;
  
  // Apply changes: first change position 0 to a
  var d1 := digits[..0] + [a] + digits[0+1..];
  assert d1 == [a] + digits[1..];
  assert |d1| == 6;
  assert forall idx :: 0 <= idx < |d1| ==> 0 <= d1[idx] <= 9;
  assert d1[0] == a;
  assert forall idx :: 1 <= idx < 6 ==> d1[idx] == digits[idx];
  
  // Then change position 1 to b
  var d2 := d1[..1] + [b] + d1[1+1..];
  assert d2 == [a] + [b] + d1[2..];
  assert d2 == [a, b] + digits[2..];
  assert |d2| == 6;
  assert forall idx :: 0 <= idx < |d2| ==> 0 <= d2[idx] <= 9;
  assert d2[0] == a && d2[1] == b;
  assert forall idx :: 2 <= idx < 6 ==> d2[idx] == digits[idx];
  
  // Finally change position 2 to c
  var d3 := d2[..2] + [c] + d2[2+1..];
  assert d3 == [a, b] + [c] + d2[3..];
  assert d3 == [a, b, c] + digits[3..];
  assert |d3| == 6;
  assert forall idx :: 0 <= idx < |d3| ==> 0 <= d3[idx] <= 9;
  assert d3[0] == a && d3[1] == b && d3[2] == c;
  assert d3[3] == digits[3] && d3[4] == digits[4] && d3[5] == digits[5];
  
  // Verify that d3 is lucky
  assert d3[0] + d3[1] + d3[2] == a + b + c == targetSum;
  assert d3[3] + d3[4] + d3[5] == digits[3] + digits[4] + digits[5] == targetSum;
  assert isLucky(d3);
  
  // Confirm the existential
  assert 0 < 1 < 2 < 6;
}
// </vc-helpers>

// <vc-spec>
method solve(ticket: string) returns (result: int)
  requires ValidTicket(ticket)
  ensures 0 <= result <= 3
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 0 <==> canMakeLuckyWith0Changes(digits)
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 1 <==> (!canMakeLuckyWith0Changes(digits) && canMakeLuckyWith1Change(digits))
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 2 <==> (!canMakeLuckyWith0Changes(digits) && !canMakeLuckyWith1Change(digits) && canMakeLuckyWith2Changes(digits))
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 3 <==> (!canMakeLuckyWith0Changes(digits) && !canMakeLuckyWith1Change(digits) && !canMakeLuckyWith2Changes(digits))
// </vc-spec>
// <vc-code>
{
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  
  // Check if already lucky (0 changes needed)
  if isLucky(digits) {
    return 0;
  }
  
  // Check if can
// </vc-code>

