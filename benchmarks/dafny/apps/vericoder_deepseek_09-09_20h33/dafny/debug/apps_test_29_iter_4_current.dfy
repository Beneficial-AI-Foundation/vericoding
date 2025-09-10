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
lemma canMakeLuckyWith1ChangeLemma(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures canMakeLuckyWith1Change(digits) == exists pos :: 0 <= pos < 6 &&
    (exists newDigit :: 0 <= newDigit <= 9 &&
      (var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
      isLucky(newDigits)))
{
}

lemma canMakeLuckyWith2ChangesLemma(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures canMakeLuckyWith2Changes(digits) == exists i, j :: 0 <= j < i < 6 &&
    (exists k, l :: 0 <= k <= 9 && 0 <= l <= 9 &&
      (var newDigits := digits[..i] + [k] + digits[i+1..];
      var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
      isLucky(finalDigits)))
{
}

lemma sumThreeDigits(a: int, b: int, c: int) returns (sum: int)
  requires 0 <= a <= 9 && 0 <= b <= 9 && 0 <= c <= 9
  ensures 0 <= sum <= 27
{
  sum := a + b + c;
}

ghost function ToSeq(ticket: string): seq<int>
  requires ValidTicket(ticket)
  ensures |ToSeq(ticket)| == 6
  ensures forall i :: 0 <= i < 6 ==> 0 <= ToSeq(ticket)[i] <= 9
{
  seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]))
}

lemma sequencePropertiesHelper(digits: seq<int>, i: int, k: int)
  requires |digits| == 6
  requires forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
  requires 0 <= i < 6
  requires 0 <= k <= 9
  ensures |digits[..i] + [k] + digits[i+1..]| == 6
  ensures forall idx :: 0 <= idx < 6 ==> 0 <= (digits[..i] + [k] + digits[i+1..])[idx] <= 9
{
}

lemma sequencePropertiesHelper2(newDigits: seq<int>, j: int, l: int)
  requires |newDigits| == 6
  requires forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
  requires 0 <= j < 6
  requires 0 <= l <= 9
  ensures |newDigits[..j] + [l] + newDigits[j+1..]| == 6
  ensures forall idx :: 0 <= idx < 6 ==> 0 <= (newDigits[..j] + [l] + newDigits[j+1..])[idx] <= 9
{
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
  var digits_g := ToSeq(ticket);
  var digits := digits_g;
  
  if isLucky(digits) {
    result := 0;
    return;
  }
  
  var found1 := false;
  var found2 := false;
  
  // Check for 1 change
  var pos := 0;
  while (pos < 6)
    invariant 0 <= pos <= 6
    invariant !found1 ==> forall p :: 0 <= p < pos ==> 
      (forall d :: 0 <= d <= 9 ==> !isLucky(digits[..p] + [d] + digits[p+1..]))
    invariant found1 ==> exists p :: 0 <= p < 6 && (exists d :: 0 <= d <= 9 && 
      isLucky(digits[..p] + [d] + digits[p+1..]))
  {
    var d := 0;
    while (d <= 9)
      invariant 0 <= d <= 10
      invariant !found1 ==> forall nd :: 0 <= nd < d ==> 
        !isLucky(digits[..pos] + [nd] + digits[pos+1..])
      invariant found1 ==> exists nd :: 0 <= nd <= 9 && 
        isLucky(digits[..pos] + [nd] + digits[pos+1..])
    {
      var newDigits := digits[..pos] + [d] + digits[pos+1..];
      sequencePropertiesHelper(digits, pos, d);
      if isLucky(newDigits) {
        found1 := true;
        break;
      }
      d := d + 1;
    }
    if found1 {
      break;
    }
    pos := pos + 1;
  }
  
  if found1 {
    result := 1;
    return;
  }
  
  // Check for 2 changes
  var i := 0;
  while (i < 6)
    invariant 0 <= i <= 6
    invariant !found2 ==> forall i1 :: 0 <= i1 < i ==> 
      (forall j :: 0 <= j < i1 ==> 
        (forall k :: 0 <= k <= 9 ==> 
          (forall l :: 0 <= l <= 9 ==> 
            |digits[..i1] + [k] + digits[i1+1..]| == 6 &&
            |(digits[..i1] + [k] + digits[i1+1..])[..j] + [l] + (digits[..i1] + [k] + digits[i1+1..])[j+1..]| == 6 &&
            forall idx :: 0 <= idx < 6 ==> 0 <= (digits[..i1] + [k] + digits[i1+1..])[idx] <= 9 &&
            !isLucky((digits[..i1] + [k] + digits[i1+1..])[..j] + [l] + (digits[..i1] + [k] + digits[i1+1..])[j+1..]))))
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j <= i
      invariant !found2 ==> forall j1 :: 0 <= j1 < j ==> 
        (forall k :: 0 <= k <= 9 ==> 
          (forall l :: 0 <= l <= 9 ==> 
            |digits[..i] + [k] + digits[i+1..]| == 6 &&
            |(digits[..i] + [k] + digits[i+1..])[..j1] + [l] + (digits[..i] + [k] + digits[i+1..])[j1+1..]| == 6 &&
            forall idx :: 0 <= idx < 6 ==> 0 <= (digits[..i] + [k] + digits[i+1..])[idx] <= 9 &&
            !isLucky((digits[..i] + [k] + digits[i+1..])[..j1] + [l] + (digits[..i] + [k] + digits[i+1..])[j1+1..])))
    {
      var k := 0;
      while (k <= 9)
        invariant 0 <= k <= 10
        invariant !found2 ==> forall k1 :: 0 <= k1 < k ==> 
          (forall l :: 0 <= l <= 9 ==> 
            |digits[..i] + [k1] + digits[i+1..]| == 6 &&
            |(digits[..i] + [k1] + digits[i+1..])[..j] + [l] + (digits[..i] + [k1] + digits[i+1..])[j+1..]| == 6 &&
            forall idx :: 0 <= idx < 6 ==> 0 <= (digits[..i] + [k1] + digits[i+1..])[idx] <= 9 &&
            !isLucky((digits[..i] + [k1] + digits[i+极..])[..j] + [l] + (digits[..i] + [k1] + digits[i+1..])[j+1..]))
      {
        var l := 0;
        while (l <= 9)
          invariant 0 <= l <= 10
          invariant !found2 ==> forall l1 :: 0 <= l1 < l ==> 
            |digits[..i] + [k] + digits[i+1..]| == 6 &&
            |(digits[..i] + [k] + digits[i+1..])[..j] + [l1] + (digits[..i] + [k] + digits[i+1..])[j+1..]| == 6 &&
            forall idx :: 0 <= idx < 6 ==> 0 <= (digits[..i] + [k] + digits[i+1..])[idx] <= 9 &&
            !isLucky((digits[..i] + [k] + digits[i+1..])[..j] + [l1] + (digits[..i] + [k] + digits[i+1..])[j+1..]))
        {
          var newDigits1 := digits[..i] + [k] + digits[i+1..];
          sequencePropertiesHelper(digits, i, k);
          var finalDigits := newDigits1[..j] + [l] + newDigits1[j+1..];
          sequencePropertiesHelper2(newDigits1, j, l);
          if isLucky(finalDigits) {
            found2 := true;
            break;
          }
          l := l + 1;
        }
        if found2 {
          break;
        }
        k := k + 1;
      }
      if found2 {
        break;
      }
      j := j + 1;
    }
    if found2 {
      break;
    }
    i := i + 1;
  }
  
  if found2 {
    result := 2;
  } else {
    result := 3;
  }
}
// </vc-code>

