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
      isLucky(d3)))
{
  // We can always set last 3 digits to 0 to make both sums equal
  var d1 := digits[..3] + [0] + digits[4..];
  assert d1 == digits[0..3] + [0] + digits[4..6];
  assert |d1| == 6;
  assert forall idx :: 0 <= idx < |d1| ==> 0 <= d1[idx] <= 9;
  
  var d2 := d1[..4] + [0] + d1[5..];
  assert |d2| == 6;
  assert forall idx :: 0 <= idx < |d2| ==> 0 <= d2[idx] <= 9;
  
  var d3 := d2[..5] + [0] + d2[6..];
  assert |d3| == 6;
  assert d3[3] == 0 && d3[4] == 0 && d3[5] == 0;
  assert d3[0] == digits[0] && d3[1] == digits[1] && d3[2] == digits[2];
  assert forall idx :: 0 <= idx < |d3| ==> 0 <= d3[idx] <= 9;
  assert d3[3] + d3[4] + d3[5] == 0;
  assert d3[0] + d3[1] + d3[2] == digits[0] + digits[1] + digits[2];
  
  // Now set first 3 digits to 0 as well
  var e1 := [0] + d3[1..];
  assert |e1| == 6;
  assert forall idx :: 0 <= idx < |e1| ==> 0 <= e1[idx] <= 9;
  
  var e2 := e1[..1] + [0] + e1[2..];
  assert |e2| == 6;
  assert forall idx :: 0 <= idx < |e2| ==> 0 <= e2[idx] <= 9;
  
  var e3 := e2[..2] + [0] + e2[3..];
  assert |e3| == 6;
  assert e3[0] == 0 && e3[1] == 0 && e3[2] == 0;
  assert e3[3] == 0 && e3[4] == 0 && e3[5] == 0;
  assert forall idx :: 0 <= idx < |e3| ==> 0 <= e3[idx] <= 9;
  assert e3[0] + e3[1] + e3[2] == 0;
  assert e3[3] + e3[4] + e3[5] == 0;
  assert isLucky(e3);
  
  // Witness: i=0, j=1, k=2 with a=0, b=0, c=0
  assert 0 < 1 < 2 < 6;
  var w1 := digits[..0] + [0] + digits[1..];
  var w2 := w1[..1] + [0] + w1[2..];
  var w3 := w2[..2] + [0] + w2[3..];
  assert w3 == e3;
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

