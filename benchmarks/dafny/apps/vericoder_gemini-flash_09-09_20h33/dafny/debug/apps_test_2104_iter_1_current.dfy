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
function int_to_string(n: int): string

lemma least_common_multiple(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) % gcd(a, b) == 0

lemma gcd_of_consecutive(a: int)
  ensures (a != 0 || a+1 != 0) ==> gcd(a, a + 1) == 1
  ensures (a != 0 || a-1 != 0) ==> gcd(a, a - 1) == 1
{
  if a == 0 {
    assert gcd(0, 1) == 1;
    assert gcd(0, -1) == 1;
  } else {
    // gcd(a, a+1) == gcd(a, (a+1) % a) == gcd(a, 1) == 1
    calc {
      gcd(a, a + 1);
      gcd(a + 1 - a, a);
      gcd(1, a);
      1;
    }
    // gcd(a, a-1) == gcd(a, (a-1) % a) == gcd(a, -1) == 1
    calc {
      gcd(a, a - 1);
      gcd(a - (a - 1), a - 1);
      gcd(1, a - 1);
      1;
    }
  }
}

lemma lemma_PairHasGcdOne_consecutive(i: int, j: int, l: int, r: int)
  requires l <= i <= r && l <= j <= r && j == i + 1
  ensures PairHasGcdOne(int_to_string(i) + " " + int_to_string(j), l, r)
{
  gcd_of_consecutive(i);
}
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
{
  var s: seq<string> := ["YES"];
  var current := l;
  while current <= r - 1
    invariant l <= current
    invariant current % 2 == l % 2
    invariant current + 1 <= r
    invariant forall i :: 1 <= i < |s| ==>
      (exists j :: l <= j <= r - 1 && j % 2 == l % 2 &&
       s[i] == int_to_string(j) + " " + int_to_string(j + 1))
    invariant |s| == 1 + (current - l) / 2
  {
    var pair_str := int_to_string(current) + " " + int_to_string(current + 1);
    s := s + [pair_str];
    lemma_PairHasGcdOne_consecutive(current, current + 1, l, r);
    current := current + 2;
  }
  result := s;
}
// </vc-code>

