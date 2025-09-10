function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0
  requires b >= 0
  decreases b
  ensures gcd > 0
  ensures forall k :: k > 0 ==> (a % k == 0 && b % k == 0) <==> k % gcd == 0
  if b == 0 then a else gcd(b, a % b)

function gcdseq(seq: seq<int>): int
  requires |seq| > 0 && forall i :: 0 <= i < |seq| ==> seq[i] > 0
  decreases |seq|
  ensures gcdseq > 0
  ensures forall k :: k > 0 ==> (forall i :: 0 <= i < |seq| ==> seq[i] % k == 0) <==> k % gcdseq == 0
  if |seq| == 1 then seq[0] else gcd(seq[0], gcdseq(seq[1..]))
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
  var d := gcdseq(a);
  var m := min(a);
  if d == m {
    result := d;
  } else {
    result := -1;
  }
}
// </vc-code>

