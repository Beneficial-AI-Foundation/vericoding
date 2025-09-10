predicate ValidInput(l: int, r: int)
{
    l < r && (r - l) % 2 == 1
}

function gcd(a: int, b: int): int
    requires a != 0 || b != 0
    decreases if a >= 0 then a else -a
{
    if a == 0 then if b >= 0 then b else -b
    else gcd(b % a, a)
}

predicate PairHasGcdOne(pair: string, l: int, r: int)
{
    exists i, j :: l <= i <= r && l <= j <= r && i != j &&
        pair == int_to_string(i) + " " + int_to_string(j) &&
        (i != 0 || j != 0) && gcd(i, j) == 1
}

predicate ValidSolution(result: seq<string>, l: int, r: int)
{
    |result| >= 1 &&
    result[0] == "YES" &&
    |result| == 1 + (r - l + 1) / 2 &&
    (forall i :: 1 <= i < |result| ==> PairHasGcdOne(result[i], l, r))
}

// <vc-helpers>
lemma PosModFacts(k: int)
  ensures k > 0 ==> (k + 1) % k == 1
  ensures true ==> k % 1 == 0
{
  if k > 0 {
    // For positive k, (k+1) % k = 1
    assert (k + 1) % k == 1;
  }
  // For any k, k % 1 == 0
  assert k % 1 == 0;
}

lemma GcdConsecutive(k: int)
  ensures gcd(k, k + 1) == 1
{
  if k == 0 {
    // gcd(0,1) returns 1 by function definition
    assert gcd(0, 1) == 1;
  } else if k > 0 {
    // Reduce using Euclidean steps for positive k:
    // gcd(k, k+1) = gcd((k+1)%k, k) = gcd(1, k) = gcd(k%1, 1) = gcd(0,1) = 1
    PosModFacts(k);
    assert gcd(k, k + 1) == gcd((k + 1) % k, k);
    assert (k + 1) % k == 1;
    assert gcd((k + 1) % k, k) == gcd(1, k);
    assert gcd(1, k) == gcd(k % 1, 1);
    assert k % 1 == 0;
    assert gcd(k % 1, 1) == gcd(0, 1);
    assert gcd(0, 1) == 1;
  } else {
    // k < 0
    // Transform to non-negative case by observing:
    // let t = -k - 1 >= 0, then (k, k+1) = (-(t+1), -t)
    // and gcd(-(t+1), -t) == gcd(t, t+1) which we reduced to positive case.
    var t := -k - 1;
    assert t >= 0;
    // We show gcd(k, k+1) == gcd(-t-1, -t)
    // by substitution k = -t-1.
    assert k == -t - 1;
    assert k + 1 == -t;
    assert gcd(k, k + 1) == gcd(-t - 1, -t);
    // Now show gcd(-t-1, -t) == gcd(t, t+1).
    // For all integers a,b with a!=0||b!=0, one can observe gcd(-a,-b) == gcd(a,b).
    // We instantiate that here by straightforward reasoning via function unrolling:
    // handle the case t == 0 separately to avoid division by zero in unrolling.
    if t == 0 {
      // t == 0 => (-t-1, -t) = (-1, 0), gcd(-1,0) = 1 and gcd(0,1) = 1
      assert gcd(-t - 1, -t) == gcd(-1, 0);
      assert gcd(-1, 0) == 1;
      assert gcd(t, t + 1) == gcd(0, 1);
      assert gcd(0, 1) == 1;
    } else {
      // t > 0: we can reduce gcd(-t-1, -t) to gcd(t, t+1) by noting the Euclidean steps
      // mirror under sign changes; instantiate reduction for this concrete pattern.
      // First reduce gcd(-t-1, -t) = gcd((-t) % (-t-1), -t-1)
      assert gcd(-t - 1, -t) == gcd((-t) % (-t - 1), -t - 1);
      // For the specific values, (-t) % (-t-1) equals 1 (mirrors positive case)
      assert (-t) % (-t - 1) == 1;
      assert gcd((-t) % (-t - 1), -t - 1) == gcd(1, -t - 1);
      assert gcd(1, -t - 1) == gcd((-t - 1) % 1, 1);
      assert (-t - 1) % 1 == 0;
      assert gcd((-t - 1) % 1, 1) == gcd(0, 1);
      assert gcd(0, 1) == 1;
      // On the other hand, for t > 0 we also have gcd(t, t+1) == 1 by the positive case
      assert gcd(t, t +
// </vc-helpers>

// <vc-spec>
method solve(l: int, r: int) returns (result: seq<string>)
    requires ValidInput(l, r)
    ensures ValidSolution(result, l, r)
    ensures |result| >= 1
    ensures result[0] == "YES"
    ensures |result| == 1 + (r - l + 1) / 2
    ensures forall i :: 1 <= i < |result| ==> 
        (exists j :: l <= j <= r - 1 && j % 2 == l % 2 && 
         result[i] == int_to_string(j) + " " + int_to_string(j + 1))
// </vc-spec>
// <vc-code>
lemma PosModFacts(k: int)
  ensures k > 0 ==> (k + 1) % k == 1
  ensures true ==> k % 1 == 0
{
  if k > 0 {
    // For positive k, (k+1) % k = 1
    assert (k + 1) % k == 1;
  }
  // For any k, k % 1 == 0
  assert k % 1 == 0;
}

lemma GcdConsecutive(k: int)
  ensures gcd(k, k + 1) == 1
{
  if k == 0 {
    // gcd(0,1) returns 1 by function definition
    assert gcd(0, 1) == 1;
  } else if k > 0 {
    // Reduce using Euclidean steps for positive k:
    // gcd(k, k+1) = gcd((k+1)%k, k) = gcd(1, k) = gcd(k%1, 1) = gcd(0,1) = 1
    PosModFacts(k);
    assert gcd(k, k + 1) == gcd((k + 1) % k, k);
    assert (k + 1) % k == 1;
    assert gcd((k + 1) % k, k) == gcd(1, k);
    assert gcd(1, k) == gcd(k % 1, 1);
    assert k % 1 == 0;
    assert gcd(k % 1, 1) == gcd(0, 1);
    assert gcd(0, 1) == 1;
  } else {
    // k < 0
    // Transform to non-negative case by observing:
    // let t = -k - 1 >= 0, then (k, k+1) = (-(t+1), -t)
    // and gcd(-(t+1), -t) == gcd(t, t+1) which we reduced to positive case.
    var t := -k - 1;
    assert t >= 0;
    // We show gcd(k, k+1) == gcd(-t-1, -t)
    // by substitution k = -t-1.
    assert k == -t - 1;
    assert k + 1 == -t;
    assert gcd(k, k + 1) == gcd(-t - 1, -t);
    // Now show gcd(-t-1, -t) == gcd(t, t+1).
    // For all integers a,b with a!=0||b!=0, one can observe gcd(-a,-b) == gcd(a,b).
    // We instantiate that here by straightforward reasoning via function unrolling:
    // handle the case t == 0 separately to avoid division by zero in unrolling.
    if t == 0 {
      // t == 0 => (-t-1, -t) = (-1, 0), gcd(-1,0) = 1 and gcd(0,1) = 1
      assert gcd(-t - 1, -t) == gcd(-1, 0);
      assert gcd(-1, 0) == 1;
      assert gcd(t, t + 1) == gcd(0, 1);
      assert gcd(0, 1) == 1;
    } else {
      // t > 0: we can reduce gcd(-t-1, -t) to gcd(t, t+1) by noting the Euclidean steps
      // mirror under sign changes; instantiate reduction for this concrete pattern.
      // First reduce gcd(-t-1, -t) = gcd((-t) % (-t-1), -t-1)
      assert gcd(-t - 1, -t) == gcd((-t) % (-t - 1), -t - 1);
      // For the specific values, (-t) % (-t-1) equals 1 (mirrors positive case)
      assert (-t) % (-t - 1) == 1;
      assert gcd((-t) % (-t - 1), -t - 1) == gcd(1, -t - 1);
      assert gcd(1, -t - 1) == gcd((-t - 1) % 1, 1);
      assert (-t - 1) % 1 == 0;
      assert gcd((-t - 1) % 1, 1) == gcd(0, 1);
      assert gcd(0, 1) == 1;
      // On the other hand, for t > 0 we also have gcd(t, t+1) == 1 by the positive case
      assert gcd(t, t +
// </vc-code>

