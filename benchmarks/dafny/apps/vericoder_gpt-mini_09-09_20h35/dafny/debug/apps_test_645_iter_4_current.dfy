predicate IsVowel(c: char) {
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate IsOddDigit(c: char) {
  c == '1' || c == '3' || c == '5' || c == '7' || c == '9'
}

predicate NeedsFlipping(c: char) {
  IsVowel(c) || IsOddDigit(c)
}

function CountFlips(s: string): int {
  |set i | 0 <= i < |s| && NeedsFlipping(s[i])|
}

// <vc-helpers>
function toString(i: int): string {
  if i == 0 then "0"
  else if i == 1 then "1"
  else if i == 2 then "2"
  else if i == 3 then "3"
  else if i == 4 then "4"
  else if i == 5 then "5"
  else if i == 6 then "6"
  else if i == 7 then "7"
  else if i == 8 then "8"
  else if i == 9 then "9"
  else if i == 10 then "10"
  else if i == 11 then "11"
  else if i == 12 then "12"
  else if i == 13 then "13"
  else if i == 14 then "14"
  else if i == 15 then "15"
  else if i == 16 then "16"
  else if i == 17 then "17"
  else if i == 18 then "18"
  else if i == 19 then "19"
  else if i == 20 then "20"
  else if i == 21 then "21"
  else if i == 22 then "22"
  else if i == 23 then "23"
  else if i == 24 then "24"
  else if i == 25 then "25"
  else if i == 26 then "26"
  else if i == 27 then "27"
  else if i == 28 then "28"
  else if i == 29 then "29"
  else if i == 30 then "30"
  else if i == 31 then "31"
  else if i == 32 then "32"
  else if i == 33 then "33"
  else if i == 34 then "34"
  else if i == 35 then "35"
  else if i == 36 then "36"
  else if i == 37 then "37"
  else if i == 38 then "38"
  else if i == 39 then "39"
  else if i == 40 then "40"
  else if i == 41 then "41"
  else if i == 42 then "42"
  else if i == 43 then "43"
  else if i == 44 then "44"
  else if i == 45 then "45"
  else if i == 46 then "46"
  else if i == 47 then "47"
  else if i == 48 then "48"
  else if i == 49 then "49"
  else if i == 50 then "50"
  else ""
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires |s| >= 1 && |s| <= 50
  ensures |result| > 0
  ensures result == toString(CountFlips(s)) + "\n"
// </vc-spec>
// <vc-code>
{
  ghost var seen: set<int> := {};
  var cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> (NeedsFlipping(s[k]) <==> k in seen)
    invariant forall k :: k in seen ==> 0 <= k < i
    invariant cnt == |seen|
  {
    if NeedsFlipping(s[i]) {
      seen := seen + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  // make the consequences of the loop invariants explicit for Dafny
  assert i == |s|;
  assert forall j :: 0 <= j < |s| ==> (NeedsFlipping(s[j]) <==> j in seen);
  assert seen == { j | 0 <= j < |s| && NeedsFlipping(s[j]) };
  assert cnt == CountFlips(s);
  result := toString(cnt) + "\n";
}
// </vc-code>

