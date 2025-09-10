predicate ValidInput(s: string, k: int)
{
    1 <= k <= 26 && 1 <= |s| <= 1000 && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function UniqueChars(s: string): set<char>
{
    set c | c in s
}

function MinChanges(s: string, k: int): int
    requires ValidInput(s, k)
    requires |s| >= k
{
    var unique := UniqueChars(s);
    if k <= |unique| then 0 else k - |unique|
}

predicate IsImpossible(s: string, k: int)
    requires ValidInput(s, k)
{
    |s| < k
}

// <vc-helpers>
lemma IntToStringLemma(n: int) returns (s: string)
  requires n >= 0
  ensures s == (if n == 0 then "0" else IntToString(n))
{
  if n == 0 {
    s := "0";
  } else {
    s := IntToString(n);
  }
}

function IntToString(n: int): string 
  requires n >= 0
  ensures n == 0 ==> IntToString(n) == "0"
  ensures n > 0 ==> |IntToString(n)| > 0
{
  if n == 0 then "0" else
    var digit := (n % 10) as int;
    var charCode := digit + 48;
    var digits := [charCode as char] + "";
    var m := n / 10;
    if m > 0 then
      IntToString(m) + digits
    else
      digits
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires ValidInput(s, k)
    ensures IsImpossible(s, k) ==> result == "impossible"
    ensures !IsImpossible(s, k) ==> result == IntToString(MinChanges(s, k))
// </vc-spec>
// <vc-code>
{
  if |s| < k {
    result := "impossible";
  } else {
    var unique := UniqueChars(s);
    var changes := k - |unique|;
    if changes < 0 {
      result := "0";
    } else {
      result := IntToString(changes);
    }
  }
}
// </vc-code>

