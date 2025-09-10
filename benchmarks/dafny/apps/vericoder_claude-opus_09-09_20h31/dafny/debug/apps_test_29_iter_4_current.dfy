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
  ensures (exists i, j, k :: 0 <= i < j < k < 6 &&
    (exists a, b, c :: 0 <= a <= 9 && 0 <= b <= 9 && 0 <= c <= 9 &&
      var d1 := digits[..i] + [a] + digits[i+1..];
      var d2 := d1[..j] + [b] + d1[j+1..];
      var d3 := d2[..k] + [c] + d2[k+1..];
      |d3| == 6 && (forall idx :: 0 <= idx < |d3| ==> 0 <= d3[idx] <= 9) && isLucky(d3)))
{
  // We can make positions 3, 4, 5 all zeros
  // This is done by changing position 3, then 4, then 5
  var d1 := digits[..3] + [0] + digits[4..];
  assert |d1| == 6;
  assert forall idx :: 0 <= idx < |d1| ==> 0 <= d1[idx] <= 9;
  assert d1[3] == 0;
  
  var d2 := d1[..4] + [0] + d1[5..];
  assert |d2| == 6;
  assert forall idx :: 0 <= idx < |d2| ==> 0 <= d2[idx] <= 9;
  assert d2[3] == 0 && d2[4] == 0;
  
  var d3 := d2[..5] + [0] + d2[6..];
  assert |d3| == 6;
  assert forall idx :: 0 <= idx < |d3| ==> 0 <= d3[idx] <= 9;
  assert d3[3] == 0 && d3[4] == 0 && d3[5] == 0;
  assert d3[3] + d3[4] + d3[5] == 0;
  assert d3[0] + d3[1] + d3[2] == digits[0] + digits[1] + digits[2];
  
  // Now we need to balance the first half
  // We know the sum of first 3 digits, let's call it S
  // We need to make it 0 as well
  // Since we can only change positions that haven't been changed yet (0, 1, 2)
  // But we've already used positions 3, 4, 5
  // Actually, let me reconsider the approach
  
  // Better approach: change positions 0, 1, 2 to all be 0
  var e1 := [0] + digits[1..];
  assert |e1| == 6;
  assert forall idx :: 0 <= idx < |e1| ==> 0 <= e1[idx] <= 9;
  
  var e2 := e1[..1] + [0] + e1[2..];
  assert |e2| == 6;
  assert forall idx :: 0 <= idx < |e2| ==> 0 <= e2[idx] <= 9;
  
  var e3 := e2[..2] + [0] + e2[3..];
  assert |e3| == 6;
  assert forall idx :: 0 <= idx < |e3| ==> 0 <= e3[idx] <= 9;
  assert e3[0] == 0 && e3[1] == 0 && e3[2] == 0;
  assert e3[0] + e3[1] + e3[2] == 0;
  assert e3[3] + e3[4] + e3[5] == digits[3] + digits[4] + digits[5];
  
  // This doesn't work either as the sums might not match
  // Let's use a different strategy: set all digits to 0
  // We can change positions 0, 3, 4 to 0
  var f1 := [0] + digits[1..];
  assert |f1| == 6;
  assert forall idx :: 0 <= idx < |f1| ==> 0 <= f1[idx] <= 9;
  
  var f2 := f1[..3] + [0] + f1[4..];
  assert |f2| == 6;
  assert forall idx :: 0 <= idx < |f2| ==> 0 <= f2[idx] <= 9;
  
  var f3 := f2[..4] + [0] + f2[5..];
  assert |f3| == 6;
  assert forall idx :: 0 <= idx < |f3| ==> 0 <= f3[idx] <= 9;
  assert f3[0] == 0 && f3[3] == 0 && f3[4] == 0;
  
  // Sum of first half: 0 + digits[1] + digits[2]
  // Sum of second half: 0 + 0 + digits[5]
  // These might not be equal
  
  // Actually, let me use positions 0, 1, 3 and set appropriate values
  // Set position 0 to 0, position 1 to 0, position 3 to sum of remaining digits in first half
  // No wait, we need to be systematic
  
  // Final approach: Use positions 0, 1, 3
  // After changing these, we want sum(0,1,2) == sum(3,4,5)
  // Currently: digits[2] on left, digits[4] + digits[5] on right
  // We need: newDigit[0] + newDigit[1] + digits[2] == newDigit[3] + digits[4] + digits[5]
  // Let's set all three to 0: 0 + 0 + digits[2] == 0 + digits[4] + digits[5]
  // This works only if digits[2] == digits[4] + digits[5]
  
  // Universal solution: positions 0, 1, 2, set all to 0
  // Then sum of first half = 0, but sum of second half = digits[3] + digits[4] + digits[5]
  // So this doesn't work unless the second half also sums to 0
  
  // Correct universal solution: Use positions 0, 1, 2
  // Set them such that sum equals 0
  // But we can only use digits 0-9, so we might not be able to achieve any sum
  
  // Actually the simplest universal solution: positions 0, 3, 4
  // Set position 0 = 0, position 3 = digits[1] + digits[2], position 4 = 0
  // But position 3 might be > 9
  
  // Let me try the original approach more carefully
  // Change positions 0, 1, 2 all to 0
  // This gives sum of first half = 0
  // Then we need sum of second half = 0 too
  // But we can't change positions 3, 4, 5 after that
  
  // OK, let's be more careful. We need i < j < k
  // Let's use i=0, j=1, k=2 and set appropriate values
  // After these changes: a, b, c, digits[3], digits[4], digits[5]
  // We want a + b + c == digits[3] + digits[4] + digits[5]
  // We can always achieve this by setting a = min(9, digits[3] + digits[4] + digits[5])
  // and b = 0, c = 0 if a is sufficient
  // Or distribute across a, b, c if needed
  
  var targetSum := digits[3] + digits[4] + digits[5];
  var a := if targetSum <= 9 then targetSum else 9;
  var b := if targetSum <= 9 then 0 else if targetSum - 9 <= 9 then targetSum - 9 else 9;
  var c := if targetSum <= 9 then 0 else if targetSum <= 18 then 0 else targetSum - 18;
  
  assert 0 <= a <= 9;
  assert 0 <= b <= 9;
  assert 0 <= c <= 9;
  assert a + b + c == targetSum || (targetSum > 27 && a + b + c == 27);
  
  // If targetSum > 27, we can't match it with 3 digits each at most 9
  // But targetSum <= 9 + 9 + 9 = 27, so this is fine
  assert targetSum <= 27;
  assert a + b + c == targetSum;
  
  var w1 := [a] + digits[1..];
  assert |w1| == 6;
  assert forall idx :: 0 <= idx < |w1| ==> 0 <= w1[idx] <= 9;
  
  var w2 := w1[..1] + [b] + w1[2..];
  assert |w2| == 6;
  assert forall idx :: 0 <= idx < |w2| ==> 0 <= w2[idx] <= 9;
  
  var w3 := w2[..2] + [c] + w2[3..];
  assert |w3| == 6;
  assert forall idx :: 0 <= idx < |w3| ==> 0 <= w3[idx] <= 9;
  assert w3[0] == a && w3[1] == b && w3[2] == c;
  assert w3[3] == digits[3] && w3[4] == digits[4] && w3[5] == digits[5];
  assert w3[0] + w3[1] + w3[2] == a + b + c == targetSum;
  assert w3[3] + w3[4] + w3[5] == digits[3] + digits[4] + digits[5] == targetSum;
  assert isLucky(w3);
  
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
  
  // Check if can be made lucky with 1 change
  var found1 := false;
  var pos := 0;
  while pos < 6 && !found1
    invariant 0 <= pos <= 6
    invariant found1 ==> canMakeLuckyWith1Change(digits)
    invariant !found1 ==> forall p :: 0 <= p < pos ==> 
      forall newDigit :: 0 <= newDigit <= 9 ==>
        var newDigits := digits[..p] + [newDigit] + digits[p+1..];
        !isLucky(newDigits)
  {
    var newDigit := 0;
    while newDigit <= 9 && !found1
      invariant 0 <= newDigit <= 10
      invariant found1 ==> canMakeLuckyWith1Change(digits)
      invariant !found1 ==> forall nd :: 0 <= nd < newDigit ==>
        var newDigits := digits[..pos] + [nd] + digits[pos+1..];
        !isLucky(newDigits)
    {
      var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
      if isLucky(newDigits) {
        found1 := true;
      }
      newDigit := newDigit + 1;
    }
    pos := pos + 1;
  }
  
  if found1 {
    assert canMakeLuckyWith1Change(digits);
    assert !canMakeLuckyWith0Changes(digits);
    return 1;
  }
  
  assert !canMakeLuckyWith1Change(digits);
  
  // Check if can be made lucky with 2 changes
  var found2 := false;
  var i := 1;
  while i < 6 && !found2
    invariant 1 <= i <= 6
    invariant found2 ==> canMakeLuckyWith2Changes(digits)
    invariant !found2 ==> forall ii, jj :: 0 <= jj < ii < i ==>
      forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
        var newDigits := digits[..ii] + [kk] + digits[ii+1..];
        var finalDigits := newDigits[..jj] + [ll] + newDigits[jj+1..];
        !isLucky(finalDigits)
  {
    var j := 0;
    while j < i && !found2
      invariant 0 <= j <= i
      invariant found2 ==> canMakeLuckyWith2Changes(digits)
      invariant !found2 ==> forall jj :: 0 <= jj < j ==>
        forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
          var newDigits := digits[..i] + [kk] + digits[i+1..];
          var finalDigits := newDigits[..jj] + [ll] + newDigits[jj+1..];
          !isLucky(finalDigits)
    {
      var k := 0;
      while k <= 9 && !found2
        invariant 0 <= k <= 10
        invariant found2 ==> canMakeLuckyWith2Changes(digits)
        invariant !found2 ==> forall kk :: 0 <= kk < k ==>
          forall ll :: 0 <= ll <= 9 ==>
            var newDigits := digits[..i] + [kk] + digits[i+1..];
            var finalDigits := newDigits[..j] + [ll] + newDigits[j+1..];
            !isLucky(finalDigits)
      {
        var l := 0;
        while l <= 9 && !found2
          invariant 0 <= l <= 10
          invariant found2 ==> canMakeLuckyWith2Changes(digits)
          invariant !found2 ==> forall ll :: 0 <= ll < l ==>
            var newDigits := digits[..i] + [k] + digits[i+1..];
            var finalDigits := newDigits[..j] + [ll] + newDigits[j+1..];
            !isLucky(finalDigits)
        {
          var newDigits := digits[..i] + [k] + digits[i+1..];
          assert |newDigits| == 6;
          assert forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9;
          var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
          assert |finalDigits| == 6;
          assert forall idx :: 0 <= idx < |finalDigits| ==> 0 <= finalDigits[idx] <= 9;
          if isLucky(finalDigits) {
            found2 := true;
          }
          l := l + 1;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  if found2 {
    assert canMakeLuckyWith2Changes(digits);
    assert !canMakeLuckyWith0Changes(digits);
    assert !canMakeLuckyWith1Change(digits);
    return 2;
  }
  
  assert !canMakeLuckyWith2Changes(digits);
  
  // If not lucky with 0, 1, or 2 changes, return 3
  canAlwaysMakeLuckyWith3Changes(digits);
  assert !canMakeLuckyWith0Changes(digits);
  assert !canMakeLuckyWith1Change(digits);
  assert !canMakeLuckyWith2Changes(digits);
  return 3;
}
// </vc-code>

